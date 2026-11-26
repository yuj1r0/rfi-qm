# Table 2 (v10 Geometric-Mean Polar Kähler Solver, c = 20, l_C = 0.05)

| Quantity                                 | Real Polar Solver | Fourier QM | Classical (Wigner) | rel. err | L1(rho) | L2(vs FFT) | L2(ray vs FD-Exp) | Nodes solver | Nodes QM |
|------------------------------------------|-------------------|------------|--------------------|----------|---------|------------|-------------------|--------------|----------|
| 1 Free dispersion, sigma(T=3)            | 1.802240          | 1.802776   | 1.799947           | 2.97e-04 | 0.0002  | 2.63e-04   | 5.44e-10          | 0+/0-        | 0+/0-    |
| 2 Double slit, rho(0,T=3.2)              | 0.2130            | 0.2129     | 0.1073             | 7.76e-04 | 0.0009  | 1.33e-03   | 4.90e-08          | 0+/0-        | 0+/0-    |
| 2 Double slit, # peaks (>5% max)         | 3                 | 3          | 1                  |          |         |            |                   |              |          |
| 3 Barrier tunneling, P(x>1.5, T=4.2)     | 0.1635            | 0.1648     | 0.0405             | 8.10e-03 | 0.0046  | 3.86e-03   | 1.87e-05          | 4+/0-        | 4+/0-    |
| 3b Asymptotic tunneling, P(x>1.5, T=9.0) | 0.3026            | 0.3034     | 0.0646             | 2.82e-03 | 0.0092  | 9.15e-03   | 3.85e-05          |              |          |
| 3 Barrier reflected-side L1 (x<-1.5)     | 0.0015            | 0.0000     |                    |          |         |            |                   |              |          |
| 4 Klein-Gordon sigma(T=3) [c=2 vs c=20]  | 1.1097            | 1.7912     |                    |          |         |            |                   |              |          |

```json
{
  "environment": {
    "python": "3.13.9",
    "numpy": "2.5.5",
    "scipy": "1.18.1",
    "platform": "macOS-26.6.2-arm64-arm-64bit-Mach-O"
  },
  "same_lattice_metric": "trapezoid-normalized, global-phase-aligned ray L2 distance",
  "conservation_metric": "relative peak-to-peak variation at saved output times",
  "c": 20.0,
  "l_C": 0.05,
  "packet_widths_in_l_C": {
    "exp1": 20.0,
    "exp2_slit": 11.0,
    "exp3": 40.0
  },
  "normalized_ray_L2_error_vs_same_lattice_matrix_exp": {
    "exp1": 5.444615730695735e-10,
    "exp2": 4.901666207183545e-08,
    "exp3_T4p2": 1.86801318259606e-05,
    "exp3_T9p0": 3.849239972895174e-05
  },
  "complex_L2_error_vs_fourier_split_step": {
    "exp1": 0.0002627311076410952,
    "exp2": 0.0013299779104316626,
    "exp3_T4p2": 0.0038638273282498464,
    "exp3_T9p0": 0.009151286545170624
  },
  "raw_lattice_norm_relative_peak_to_peak_variation": {
    "exp1": 1.5543122344752188e-15,
    "exp2": 5.218048215738235e-15,
    "exp3": 2.109423746787797e-15,
    "exp3_T9p0": 3.180899987853535e-12
  },
  "raw_lattice_energy_relative_peak_to_peak_variation": {
    "exp1": 9.47223463037865e-14,
    "exp2": 1.1618433708389448e-10,
    "exp3": 7.603468799592679e-09,
    "exp3_T9p0": 2.3550373508928678e-08
  },
  "max_v_over_c": {
    "exp1": 0.06823033097875916,
    "exp2": 0.13652126172686457,
    "exp3": 1.5489252321799836,
    "exp3_v0": 0.1
  },
  "min_raw_rho": {
    "exp1": 5.530709549844416e-50,
    "exp2": 6.19348308005488e-185,
    "exp3": 7.756927158246164e-66
  },
  "exp3_wigner_fraction_E_above_V0": 0.06227,
  "exp3_quantum_to_classical_ratio": 4.065145178641787,
  "exp3_asymptotic_T9": {
    "T_sim": 0.3025609583459258,
    "T_qm": 0.3034156270058801,
    "T_stationary_scattering_2pt": 0.30119747794691437,
    "stationary_momentum_tail_sigma": 8.0,
    "stationary_momentum_points": 2001,
    "T_cl": 0.0646175,
    "quantum_to_classical_ratio": 4.695564313164083
  },
  "exp4_kg_sigma_c2": 1.1097296831758963,
  "exp4_kg_sigma_c20": 1.7911678110526514,
  "runtime_s": 51.369285106658936
}
```
