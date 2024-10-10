
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following refutation as produced by
random generation of polynomials:
'(2 * x**2 + 2 * y**2 + 0 * x + 0 * y + 2 * x * y) % 4' (0, 42, 306, 307, 308, 309, 310, 358, 360, 363, 366, 369, 3252, 3253, 3254, 3255, 3256, 3257, 3258, 3259, 3260, 3261, 3262, 3263, 3264, 3265, 3266, 3455, 3456, 3457, 3458, 3459, 3460, 3461, 3462, 3463, 3464, 3465, 3466, 3467, 3468, 3469, 3861, 3863, 3866, 3869, 3872, 3876, 3879, 3882, 3886, 3889, 3892, 3896, 3900, 3904, 3908, 4064, 4066, 4069, 4072, 4075, 4079, 4082, 4085, 4089, 4092, 4095, 4099, 4103, 4107, 4111, 4267, 4268, 4269, 4270, 4281, 4282, 4283, 4284, 4285, 4286, 4287, 4288, 4313, 4314, 4315, 4316, 4317, 4318, 4338, 4339, 4340, 4341, 4356, 4357, 4358, 4359, 4360, 4379, 4381, 4384, 4387, 4390, 4394, 4397, 4400, 4404, 4407, 4410, 4414, 4418, 4422, 4426, 4431, 4434, 4437, 4441, 4444, 4447, 4451, 4455, 4459, 4463, 4468, 4471, 4474, 4478, 4481, 4484, 4488, 4492, 4496, 4500, 4505, 4509, 4513, 4517, 4522, 4526, 4530, 4534, 4539, 4543, 4547, 4551, 4556, 4561, 4566, 4571, 4576, 4583, 4586, 4589, 4592, 4598, 4601, 4605, 4610, 4614, 4618, 4621, 4624, 4630, 4634, 4637, 4641, 4644, 4648, 4654, 4662, 4665, 4668, 4674, 4676, 4681, 4688, 4692)
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly 2 * x² + 2 * y² + 2 * x * y % 4» : Magma (Fin 4) where
  op := memoFinOp fun x y => 2 * x*x + 2 * y*y + 2 * x * y

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly 2 * x² + 2 * y² + 2 * x * y % 4» :
  ∃ (G : Type) (_ : Magma G), Facts G [311, 370, 4577] [47, 99, 151, 203, 255, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3268, 3271, 3272, 3278, 3279, 3281, 3306, 3308, 3309, 3315, 3316, 3318, 3319, 3342, 3343, 3345, 3346, 3352, 3353, 3355, 3472, 3474, 3475, 3481, 3482, 3484, 3509, 3511, 3512, 3518, 3519, 3521, 3522, 3545, 3546, 3548, 3549, 3555, 3556, 3558, 3659, 3865, 3868, 3871, 3878, 3881, 3888, 3915, 3917, 3918, 3924, 3925, 3927, 3928, 3951, 3952, 3954, 3955, 3961, 3962, 3964, 4066, 4068, 4071, 4074, 4084, 4091, 4118, 4120, 4121, 4127, 4128, 4130, 4131, 4154, 4155, 4157, 4158, 4164, 4165, 4167, 4272, 4273, 4275, 4276, 4290, 4291, 4293, 4320, 4321, 4343, 4396, 4399, 4406, 4433, 4436, 4443, 4470, 4473, 4480, 4583, 4585, 4588, 4591, 4598, 4605, 4608, 4629, 4636, 4658] :=
    ⟨Fin 4, «FinitePoly 2 * x² + 2 * y² + 2 * x * y % 4», by decideFin!⟩
