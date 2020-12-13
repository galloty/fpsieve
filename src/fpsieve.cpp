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

// Peter L. Montgomery, Modular multiplication without trial division, Math. Comp.44 (1985), 519–521.
class MpArith
{
private:
	const uint64_t _p, _q;
	const uint64_t _one;	// 2^64 mod p
	// const uint64_t _r2;		// (2^64)^2 mod p

private:
	// p * p_inv = 1 (mod 2^64) (Newton's method)
	static uint64_t invert(const uint64_t p)
	{
		uint64_t p_inv = 1, prev = 0;
		while (p_inv != prev) { prev = p_inv; p_inv *= 2 - p * p_inv; }
		return p_inv;
	}

	uint64_t REDC(const __uint128_t t) const
	{
		const uint64_t m = uint64_t(t) * _q;
		const int64_t r = int64_t((t >> 64) - uint64_t((m * __uint128_t(_p)) >> 64));
		return (r < 0) ? uint64_t(r + _p) : uint64_t(r);
	}

	// uint64_t two_pow_64() const
	// {
	// 	uint64_t t = add(_one, _one); t = add(t, t);	// 4
	// 	for (size_t i = 0; i < 5; ++i) t = mul(t, t);	// 4^{2^5} = 2^64
	// 	return uint64_t(t);
	// }

public:
	MpArith(const uint64_t p) : _p(p), _q(invert(p)), _one((-p) % p) {}	//, _r2(two_pow_64()) { }

	// uint64_t toMp(const uint64_t n) const { return mul(n, _r2); }
	// uint64_t toInt(const uint64_t r) const { return REDC(r); }

	uint64_t one() const { return _one; }

	uint64_t add(const uint64_t a, const uint64_t b) const
	{
		const uint64_t c = (a >= _p - b) ? _p : 0;
		return a + b - c;
	}

	uint64_t sub(const uint64_t a, const uint64_t b) const
	{
		const uint64_t c = (a < b) ? _p : 0;
		return a - b + c;
	}

	uint64_t mul(const uint64_t a, const uint64_t b) const
	{
		return REDC(a * __uint128_t(b));
	}
};

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

	std::vector<bool> _sieve_m, _sieve_p;

	static const size_t max_queue_size = 1024;

	std::mutex _p_queue_mutex;
	std::queue<PArray> _p_queue;
	bool _end_range = false;
	std::atomic<size_t> _running_threads = 0;

	std::mutex _output_mutex;
	std::atomic<uint64_t> _p_cur = 0;

private:
	void prime_gen()
	{
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

		const uint64_t p0 = ((1000000000 * _p_min) / sp_max) * sp_max, p1 = ((1000000000 * _p_max) / sp_max + 1) * sp_max;

		std::cout << ", " << ((p0 == 0) ? 3 : p0) << " <= p <= " << p1 << std::endl;

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
				// std::cout << "prime_gen: waiting... p ~ " << jp + 1 << std::endl;
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
			/*logFile.flush();*/ logFile.close();
		}
	}

	void check(const uint64_t * const p_vect)
	{
		uint32_t n_min = _n_min, n_count = _n_count;

		// parallel x 4
		for (size_t j = 0; j < p_size; j += 4)
		{
			uint64_t p[4]; for (size_t k = 0; k < 4; ++k) p[k] = p_vect[j + k];
			MpArith mp_0(p[0]), mp_1(p[1]), mp_2(p[2]), mp_3(p[3]);

			uint64_t one[4]; one[0] = mp_0.one(); one[1] = mp_1.one(); one[2] = mp_2.one(); one[3] = mp_3.one();
			uint64_t minus_one[4]; minus_one[0] = mp_0.sub(0, one[0]); minus_one[1] = mp_1.sub(0, one[1]); minus_one[2] = mp_2.sub(0, one[2]); minus_one[3] = mp_3.sub(0, one[3]);

			// ri = residue of i, rf = residue of i!
			uint64_t ri[4], rf[4]; for (size_t k = 0; k < 4; ++k) rf[k] = ri[k] = one[k];

			for (uint64_t i = 2; i < n_min; ++i)
			{
				ri[0] = mp_0.add(ri[0], one[0]); ri[1] = mp_1.add(ri[1], one[1]); ri[2] = mp_2.add(ri[2], one[2]); ri[3] = mp_3.add(ri[3], one[3]);
				rf[0] = mp_0.mul(rf[0], ri[0]); rf[1] = mp_1.mul(rf[1], ri[1]); rf[2] = mp_2.mul(rf[2], ri[2]); rf[3] = mp_3.mul(rf[3], ri[3]);
			}

			for (uint32_t i = 0; i < n_count; ++i)
			{
				ri[0] = mp_0.add(ri[0], one[0]); ri[1] = mp_1.add(ri[1], one[1]); ri[2] = mp_2.add(ri[2], one[2]); ri[3] = mp_3.add(ri[3], one[3]);
				rf[0] = mp_0.mul(rf[0], ri[0]); rf[1] = mp_1.mul(rf[1], ri[1]); rf[2] = mp_2.mul(rf[2], ri[2]); rf[3] = mp_3.mul(rf[3], ri[3]);

				bool found_neg = (rf[0] == one[0]) | (rf[1] == one[1]) | (rf[2] == one[2]) | (rf[3] == one[3]);
				bool found_pos = (rf[0] == minus_one[0]) | (rf[1] == minus_one[1]) | (rf[2] == minus_one[2]) | (rf[3] == minus_one[3]);
				if (found_neg | found_pos)
				{
					for (size_t k = 0; k < 4; ++k)
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
		: _n_min(n_min), _n_count(n_count), _p_min(p_min), _p_max(p_max)
	{
		_sieve_m.resize(n_count, false); _sieve_p.resize(n_count, false);

		std::thread t_gen_p([=] { prime_gen(); }); t_gen_p.detach();
		std::this_thread::sleep_for(std::chrono::milliseconds(100));
		for (size_t i = 0; i < thread_count; ++i)
		{
			_running_threads++;
			std::thread t_test_p([=] { find_factors(); }); t_test_p.detach();
		}

		const uint64_t p2 = 1000000000 * _p_max;
		auto t0 = std::chrono::steady_clock::now();
		uint64_t p0 = 0;

		while (_running_threads != 0)
		{
			std::this_thread::sleep_for(std::chrono::seconds(5));
			const uint64_t p1 = _p_cur;
			const auto t1 = std::chrono::steady_clock::now();
			const std::chrono::duration<double> dt = t1 - t0;
			if (p0 != 0)
			{
				const double speed = (p1 / log(p1) - p0 / log(p0)) / dt.count();
				const double eta = dt.count() / (p1 - p0) * (p2 - p1);
				std::lock_guard<std::mutex> guard(_output_mutex);
				size_t count_m = 0; for (bool b : _sieve_m) count_m += b ? 1 : 0;
				size_t count_p = 0; for (bool b : _sieve_p) count_p += b ? 1 : 0;
				std::cout << "p = " << p1 << ", "
					<< count_m << "/" << n_count << " factors+, " << count_p << "/" << n_count << " factors-, "
				 	<< int(speed) << " p/sec, ETA = " << int(eta / 60.0) << " min      \r";
			}
			t0 = t1; p0 = p1;
		}
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
	std::cerr << "   p_min: the start of the factor range, in M (10^9) values (default 0)" << std::endl;
	std::cerr << "   p_max: the end of the factor range, in M (10^9) values (default p_min + 1)" << std::endl << std::endl;

	const size_t n_threads = (argc > 1) ? std::atoi(argv[1]) : 3;
	const uint32_t n_min = (argc > 2) ? std::min(std::atoi(argv[2]), 2) : 300000;
	const uint32_t n_count = (argc > 3) ? std::min(std::atoi(argv[3]), 2) : 100000;
	const uint64_t p_min = (argc > 4) ? std::min(std::atoll(argv[4]), 18446744073708ll) : 0;
	const uint64_t p_max = (argc > 5) ? std::min(std::atoll(argv[5]), 18446744073709ll) : p_min + 1;

	std::cout << " Sieving: " << n_min << " <= n <= " << n_min + n_count;

	Sieve(n_min, n_count, p_min, p_max, n_threads);

	return EXIT_SUCCESS;
}
