/*
Copyright 2020, Yves Gallot

fpsieve is free source code, under the MIT license (see LICENSE). You can redistribute, use and/or modify it.
Please give feedback to the authors if improvement is realized. It is distributed in the hope that it will be useful.
*/

#include <cstdint>
#define _USE_MATH_DEFINES
#include <cmath>
#include <iostream>
#include <fstream>
#include <sstream>
#include <queue>
#include <vector>
#include <thread>
#include <mutex>
#include <atomic>
#include <chrono>

#define		MEGA	1000000
#define		GIGA	1000000000
#define		P_UNIT	GIGA

#define		VECTOR_SIZE		4		// must be a power of two

// Peter L. Montgomery, Modular multiplication without trial division, Math. Comp.44 (1985), 519–521.

// Arithmetic on vectors: hide the latency of the MUL instruction.

// Montgomery form: if 0 <= a < p then r is 2^64 * a mod p
template <size_t N>
class MpRes
{
private:
	uint64_t _r[N];

public:
	uint64_t operator [](const size_t i) const { return _r[i]; }
	uint64_t & operator [](const size_t i) { return _r[i]; }
};

// Montgomery modular arithmetic in Z/pZ
template <size_t N>
class MpArith
{
private:
	uint64_t _p[N], _q[N];
	MpRes<N> _one;		// 2^64 mod p
	MpRes<N> _r2;		// (2^64)^2 mod p

private:
	// p * p_inv = 1 (mod 2^64) (Newton's method)
	constexpr uint64_t invert(const uint64_t p)
	{
		uint64_t p_inv = 1, prev = 0;
		while (p_inv != prev) { prev = p_inv; p_inv *= 2 - p * p_inv; }
		return p_inv;
	}

	// The Montgomery REDC algorithm
	constexpr uint64_t REDC(const __uint128_t t, const uint64_t p, const uint64_t q) const
	{
		const uint64_t m = uint64_t(t) * q;
		const uint64_t t_hi = uint64_t(t >> 64), mp = uint64_t((m * __uint128_t(p)) >> 64);
		const uint64_t r = t_hi - mp;
		return (t_hi < mp) ? r + p : r;
	}

public:
	MpArith(const uint64_t * const p)
	{
		for (size_t k = 0; k < N; ++k)
		{
			const uint64_t p_k = p[k];
			_p[k] = p_k;
			_q[k] = invert(p_k);
			_one[k] = (-p_k) % p_k;
		}
		
		MpRes<N> t = add(_one, _one); t = add(t, t);	// 4
		for (size_t i = 0; i < 5; ++i) t = mul(t, t);	// 4^{2^5} = 2^64
		_r2 = t;
	}

	// Convert n to Montgomery representation
	MpRes<N> toMp(const uint64_t n) const
	{
		// n * (2^64)^2 = (n * 2^64) * (1 * 2^64)
		MpRes<N> r;
		for (size_t k = 0; k < N; ++k) r[k] = n;
		return mul(r, _r2);
	}

	static MpRes<N> zero()
	{
		MpRes<N> r;
		for (size_t k = 0; k < N; ++k) r[k] = 0;
		return r;
	}

	MpRes<N> one() const { return _one; }	// Montgomery form of 1

	static bool at_least_one_is_equal(const MpRes<N> & a, const MpRes<N> & b)
	{
		bool is_equal = false;
		for (size_t k = 0; k < N; ++k) is_equal |= (a[k] == b[k]);
		return is_equal;
	}

	MpRes<N> add(const MpRes<N> & a, const MpRes<N> & b) const
	{
		MpRes<N> r;
		for (size_t k = 0; k < N; ++k)
		{
			const uint64_t c = (a[k] >= _p[k] - b[k]) ? _p[k] : 0;
			r[k] = a[k] + b[k] - c;
		}
		return r;
	}

	MpRes<N> sub(const MpRes<N> & a, const MpRes<N> & b) const
	{
		MpRes<N> r;
		for (size_t k = 0; k < N; ++k)
		{
			const uint64_t c = (a[k] < b[k]) ? _p[k] : 0;
			r[k] = a[k] - b[k] + c;
		}
		return r;
	}

	MpRes<N> mul(const MpRes<N> & a, const MpRes<N> & b) const
	{
		MpRes<N> r;
		for (size_t k = 0; k < N; ++k)
		{
			r[k] = REDC(a[k] * __uint128_t(b[k]), _p[k], _q[k]);
		}
		return r;
	}
};

typedef MpRes<VECTOR_SIZE> MpResVec;
typedef MpArith<VECTOR_SIZE> MpArithVec;

class Sieve
{
private:
	static const size_t p_size = 1024;

	struct PArray
	{
		uint64_t data[p_size];	// 8 KB
	};

private:
	const uint32_t _n_min, _n_count;
	const uint64_t _p_min, _p_max;
	const size_t _thread_count;

	std::vector<bool> _sieve_m, _sieve_p;

	static const size_t max_queue_size = 1024;

	std::mutex _p_queue_mutex;
	std::queue<PArray> _p_queue;
	bool _end_range = false;
	std::atomic<size_t> _running_threads;

	std::mutex _output_mutex;
	std::atomic<uint64_t> _p_cur;

private:
	void pseudo_prime_gen()
	{
		// Segmented sieve of Eratosthenes: outputs have no factor < 2^16.
		static const uint32_t sp_max = 1 << 16;
		static const size_t sieve_size = sp_max / 2;	// sieve with an odd prime table.
		static const size_t odd_prime_count = 6541;		// # odd primes with p < 2^16.

		bool sieve[sieve_size];
		uint32_t prm[odd_prime_count];
		uint32_t prm_ptr[odd_prime_count];

		prm[0] = 3; prm[1] = 5; prm[2] = 7;
		uint32_t i = 3;
		for (uint32_t k = 11; k < sp_max; k += 2)
		{
			const uint32_t s = uint32_t(std::sqrt(double(k))) + 1;
			uint32_t d; for (d = 3; d <= s; d += 2) if (k % d == 0) break;
			if (d > s) prm[i++] = k;
		}

		// if (i != odd_prime_count) throw;

		for (size_t k = 0; k < sieve_size; ++k) sieve[k] = false;

		const uint64_t p0 = ((P_UNIT * _p_min) / sp_max) * sp_max, p1 = ((P_UNIT * _p_max) / sp_max + 1) * sp_max;

		{
			std::lock_guard<std::mutex> guard(_output_mutex);
			std::cout << ", " << ((p0 == 0) ? 3 : p0) << " <= p <= " << p1 << ", " << _thread_count << " thread(s)" << std::endl;
		}

		if (_p_min == 0)
		{
			sieve[0] = true;	// p = 1
			for (size_t i = 0; i < odd_prime_count; ++i)
			{
				const size_t p = prm[i];
				bool first = true;
				size_t k = (p - 1) / 2;
				for (; k < sieve_size; k += p) if (first) first = false; else sieve[k] = true;
				prm_ptr[i] = uint32_t(k - sieve_size);
			}
		}
		else
		{
			for (size_t i = 0; i < odd_prime_count; ++i)
			{
				const size_t p = prm[i];
				size_t o = p - size_t(p0 % p); if (o % 2 == 0) o += p;
				size_t k = (o - 1) / 2;
				for (; k < sieve_size; k += p) sieve[k] = true;
				prm_ptr[i] = uint32_t(k - sieve_size);
			}
		}

		PArray p_array;
		size_t p_array_i = 0;
		size_t queue_size = 0;

		for (uint64_t jp = p0; true; jp += sp_max)
		{
			for (size_t kp = 0; kp < sieve_size; ++kp)
			{
				if (!sieve[kp])
				{
					const uint64_t p = jp + 2 * kp + 1;
					p_array.data[p_array_i] = p;
					p_array_i = (p_array_i + 1) % p_size;
					if (p_array_i == 0)
					{
						std::lock_guard<std::mutex> guard(_p_queue_mutex);
						_p_queue.push(p_array);
						queue_size = _p_queue.size();
						if (p >= p1)
						{
							_end_range = true;
							return;
						}
					}
				}
			}

			for (size_t k = 0; k < sieve_size; ++k) sieve[k] = false;

			for (size_t i = 0; i < odd_prime_count; ++i)
			{
				size_t k = prm_ptr[i], p = prm[i];
				for (; k < sieve_size; k += p) sieve[k] = true;
				prm_ptr[i] = uint32_t(k - sieve_size);
			}

			while (queue_size > max_queue_size)
			{
				std::this_thread::sleep_for(std::chrono::milliseconds(100));
				std::lock_guard<std::mutex> guard(_p_queue_mutex);
				queue_size = _p_queue.size();
			}
		}
	}

	void output(const uint64_t p, const uint32_t n, const bool positive, const size_t index)
	{
		const char sign = positive ? '+' : '-';
		std::stringstream ss; ss << p << " | " << n << "!" << sign << "1";
		auto & sieve = positive ? _sieve_p : _sieve_m;
		std::lock_guard<std::mutex> guard(_output_mutex);
		// if (sieve[index]) return;	// no duplicate
		sieve[index] = true;
		// std::cout << ss.str() << "                 " << std::endl;
		std::ofstream logFile("fpsieve.log", std::ios::app);
		if (logFile.is_open())
		{
			logFile << ss.str() << std::endl;
			logFile.flush(); logFile.close();
		}
	}

	void check(const uint64_t * const p_vect)
	{
		uint32_t n_min = _n_min, n_count = _n_count;

		// if i <= n_pair then (i - 1) * i < p. Compute n! = (2 * 3) * (4 * 5) * ... * ((n - 1) * n)
		const uint32_t n_pair = std::max(2u, std::min(n_min, uint32_t(std::sqrt(double(p_vect[0]))) & ~1u));

		// parallel x VECTOR_SIZE
		for (size_t j = 0; j < p_size; j += VECTOR_SIZE)
		{
			const uint64_t * const p = &p_vect[j];
			MpArithVec mp(p);

			const MpResVec one = mp.one(), minus_one = mp.sub(mp.zero(), one), two = mp.add(one, one), four = mp.add(two, two), eight = mp.add(four, four);

			// ri = residue of i, rf = residue of i!
			MpResVec ri = one, rf = one;
			// residue of i * (i + 1), the step is (i + 2) * (i + 3) - i * (i + 1) = 4 * i + 6
			MpResVec r_ixip1 = mp.zero(), r_step = mp.add(four, two);

			// Factorial with pairs of numbers: i! = ((i - 1) * i) * (i - 2)!
			for (uint64_t i = 2; i < n_pair; i += 2)
			{
				r_ixip1 = mp.add(r_ixip1, r_step);
				r_step = mp.add(r_step, eight);
				rf = mp.mul(rf, r_ixip1);
			}

			// Factorial: i! = i * (i - 1)!
			ri = mp.toMp(n_pair - 1);
			for (uint64_t i = n_pair; i < n_min; ++i)
			{
				ri = mp.add(ri, one);
				rf = mp.mul(rf, ri);
			}

			// Factorial and check if i! = +/-1
			for (uint32_t i = 0; i < n_count; ++i)
			{
				ri = mp.add(ri, one);
				rf = mp.mul(rf, ri);

				if (MpArithVec::at_least_one_is_equal(rf, one) | MpArithVec::at_least_one_is_equal(rf, minus_one))
				{
					for (size_t k = 0; k < VECTOR_SIZE; ++k)
					{
						if (rf[k] == one[k]) output(p[k], n_min + i, false, i);
						if (rf[k] == minus_one[k]) output(p[k], n_min + i, true, i);
					}
				}
			}
		}
	}

	void find_factors()
	{
		PArray p_array;

		while (true)
		{
			bool found = false;
			{
				std::lock_guard<std::mutex> guard(_p_queue_mutex);
				if (!_p_queue.empty())
				{
					found = true;
					p_array = _p_queue.front();
					_p_queue.pop();
				}
			}

			if (!found)
			{
				if (_end_range) { _running_threads--; return; }
				// std::cout << "Waiting input..." << std::endl;
				std::this_thread::sleep_for(std::chrono::milliseconds(10));
			}
			else
			{
				check(p_array.data);
				const uint64_t & p = p_array.data[p_size - 1];
				_p_cur = std::max(uint64_t(_p_cur), p);
			}
		}
	}

public:
	Sieve(const uint32_t n_min, const uint32_t n_count, const uint64_t p_min, const uint64_t p_max, const size_t thread_count)
		: _n_min(n_min), _n_count(n_count), _p_min(p_min), _p_max(p_max), _thread_count(thread_count)
	{
		_sieve_m.resize(n_count, false); _sieve_p.resize(n_count, false);

		_running_threads = 0;
		_p_cur = 0;

		std::thread t_gen_p([=] { pseudo_prime_gen(); }); t_gen_p.detach();
		std::this_thread::sleep_for(std::chrono::milliseconds(100));
		for (size_t i = 0; i < thread_count; ++i)
		{
			_running_threads++;
			std::thread t_test_p([=] { find_factors(); }); t_test_p.detach();
		}

		const uint64_t p_end = P_UNIT * _p_max;
		const auto start = std::chrono::steady_clock::now();

		uint64_t p_prev = 0;
		auto t0 = start;
		double eta = 20;

		while (_running_threads != 0)
		{
			std::this_thread::sleep_for((eta >= 20) ? std::chrono::seconds(10) : std::chrono::seconds(1));
			const uint64_t p_cur = _p_cur;
			const auto t1 = std::chrono::steady_clock::now();
			const std::chrono::duration<double> dt = t1 - t0;
			if (p_prev != 0)
			{
				const double speed = (p_cur / log(p_cur) - p_prev / log(p_prev)) / dt.count();
				eta = (p_cur == p_prev) ? 0.0 : std::max(dt.count() / (p_cur - p_prev) * int64_t(p_end - p_cur), 0.0);
				std::lock_guard<std::mutex> guard(_output_mutex);
				size_t count_m = 0; for (bool b : _sieve_m) count_m += b ? 1 : 0;
				size_t count_p = 0; for (bool b : _sieve_p) count_p += b ? 1 : 0;
				std::cout << "p = " << p_cur << ", "
					<< count_m << "/" << n_count << " factors+, " << count_p << "/" << n_count << " factors-, "
				 	<< int(speed) << " p/sec, ETA = " << int(eta / 60.0) << " min      \r";
			}
			t0 = t1; p_prev = p_cur;
		}

		const std::chrono::duration<double> dt = std::chrono::steady_clock::now() - start;
		const uint64_t p_start = P_UNIT * _p_min;
		const double speed = (p_prev / log(p_prev) - p_start / log(p_start)) / dt.count();
		size_t count_m = 0; for (bool b : _sieve_m) count_m += b ? 1 : 0;
		size_t count_p = 0; for (bool b : _sieve_p) count_p += b ? 1 : 0;
		std::cout << count_m << "/" << n_count << " factors+, " << count_p << "/" << n_count << " factors-, "
				  << int(speed) << " p/sec, " << int(dt.count()) << " sec.                                  " << std::endl;
	}

	virtual ~Sieve() {}
};

int main(int argc, char * argv[])
{
	std::cerr << "fpsieve: sieve factorial numbers" << std::endl;
	std::cerr << " Copyright (c) 2020, Yves Gallot" << std::endl;
	std::cerr << " fpsieve is free source code, under the MIT license." << std::endl << std::endl;
	std::cerr << " Usage: fpsieve <n_threads> <n_min> <n_count> <p_min> <p_max>" << std::endl;
	std::cerr << "   n_threads: the number of threads (default 3)" << std::endl;
	std::cerr << "   n_min: the minimum n (n! +/- 1) to search (default 300000)" << std::endl;
	std::cerr << "   n_count: the number of n to search (default 100000)" << std::endl;
	std::cerr << "   p_min: the start of the factor range, in Giga (10^9) values (default 0)" << std::endl;
	std::cerr << "   p_max: the end of the factor range, in Giga (10^9) values (default p_min + 1)" << std::endl << std::endl;

	const size_t n_threads = (argc > 1) ? std::atoi(argv[1]) : 3;
	const uint32_t n_min = (argc > 2) ? (std::max(std::atoi(argv[2]), 2) & ~1) : 300000;	// even
	const uint32_t n_count = (argc > 3) ? (std::max(std::atoi(argv[3]), 2) & ~1) : 100000;	// even
	const uint64_t p_min = (argc > 4) ? std::min(std::atoll(argv[4]), 18446744073708ll) : 0;
	const uint64_t p_max = (argc > 5) ? std::min(std::atoll(argv[5]), 18446744073709ll) : p_min + 1;

	std::cout << " Sieving: " << n_min << " <= n <= " << n_min + n_count;

	Sieve(n_min, n_count, p_min, p_max, n_threads);

	return EXIT_SUCCESS;
}
