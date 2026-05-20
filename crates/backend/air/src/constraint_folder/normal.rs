use crate::*;
use field::*;
use poly::*;

#[derive(Debug)]
pub struct ConstraintFolder<'a, IF, EF: ExtensionField<PF<EF>>, ExtraData: AlphaPowers<EF>> {
    pub flat: &'a [IF],
    pub shift: &'a [IF],
    pub extra_data: &'a ExtraData,
    pub accumulator: EF,
    pub constraint_index: usize,
    /// Controls whether `assert_zero[_ef]` / `assert_zero_linear` accumulate or just
    /// bump `constraint_index`. See [`FolderMode`].
    pub mode: FolderMode,
}

impl<'a, IF, EF, ExtraData> ConstraintFolder<'a, IF, EF, ExtraData>
where
    EF: ExtensionField<PF<EF>>,
    ExtraData: AlphaPowers<EF>,
{
    pub fn new(flat: &'a [IF], shift: &'a [IF], extra_data: &'a ExtraData) -> Self {
        Self {
            flat,
            shift,
            extra_data,
            accumulator: EF::ZERO,
            constraint_index: 0,
            mode: FolderMode::All,
        }
    }
}

impl<'a, IF, EF, ExtraData> AirBuilder for ConstraintFolder<'a, IF, EF, ExtraData>
where
    IF: Algebra<PF<EF>> + 'static,
    EF: Field + ExtensionField<PF<EF>> + Mul<IF, Output = EF> + Add<IF, Output = EF>,
    ExtraData: AlphaPowers<EF>,
{
    type F = PF<EF>;
    type IF = IF;
    type EF = EF;

    #[inline]
    fn flat(&self) -> &[Self::IF] {
        self.flat
    }

    #[inline]
    fn shift(&self) -> &[Self::IF] {
        self.shift
    }

    #[inline]
    fn assert_zero(&mut self, x: IF) {
        if matches!(self.mode, FolderMode::All | FolderMode::HighOnly) {
            let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
            self.accumulator += alpha_power * x;
        }
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_ef(&mut self, x: EF) {
        if matches!(self.mode, FolderMode::All | FolderMode::HighOnly) {
            let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
            self.accumulator += alpha_power * x;
        }
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_linear(&mut self, x: IF) {
        if matches!(self.mode, FolderMode::All | FolderMode::LinearOnly) {
            let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
            self.accumulator += alpha_power * x;
        }
        self.constraint_index += 1;
    }
}
