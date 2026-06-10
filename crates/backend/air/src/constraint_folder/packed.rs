use crate::*;
use field::*;
use poly::*;

#[derive(Debug)]
pub struct ConstraintFolderPacked<'a, IF, EF: ExtensionField<PF<EF>>, ExtraData: AlphaPowers<EF>> {
    pub flat: &'a [IF],
    pub shift: &'a [IF],
    pub extra_data: &'a ExtraData,
    pub accumulator: EFPacking<EF>,
    pub constraint_index: usize,
}

impl<'a, IF, EF, ExtraData> ConstraintFolderPacked<'a, IF, EF, ExtraData>
where
    EF: ExtensionField<PF<EF>>,
    EFPacking<EF>: PrimeCharacteristicRing,
    ExtraData: AlphaPowers<EF>,
{
    pub fn new(flat: &'a [IF], shift: &'a [IF], extra_data: &'a ExtraData) -> Self {
        Self {
            flat,
            shift,
            extra_data,
            accumulator: EFPacking::<EF>::ZERO,
            constraint_index: 0,
        }
    }
}

impl<'a, IF, EF, ExtraData> AirBuilder for ConstraintFolderPacked<'a, IF, EF, ExtraData>
where
    IF: Algebra<PFPacking<EF>> + 'static,
    EF: Field + ExtensionField<PF<EF>>,
    EFPacking<EF>: PrimeCharacteristicRing + Mul<IF, Output = EFPacking<EF>> + Add<IF, Output = EFPacking<EF>>,
    ExtraData: AlphaPowers<EF>,
{
    type F = PFPacking<EF>;
    type IF = IF;
    type EF = EFPacking<EF>;

    #[inline]
    fn flat(&self) -> &[Self::IF] {
        self.flat
    }

    #[inline]
    fn shift(&self) -> &[Self::IF] {
        self.shift
    }

    #[inline(always)]
    fn assert_zero(&mut self, x: IF) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += EFPacking::<EF>::from(alpha_power) * x;
        self.constraint_index += 1;
    }

    #[inline(always)]
    fn assert_zero_ef(&mut self, x: EFPacking<EF>) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += EFPacking::<EF>::from(alpha_power) * x;
        self.constraint_index += 1;
    }
}
