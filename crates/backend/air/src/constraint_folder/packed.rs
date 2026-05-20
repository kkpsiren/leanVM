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
    pub skip_low: bool,
    pub accumulator_low: EFPacking<EF>,
    pub cached_state: Option<Vec<IF>>,
    pub low_ci_count: usize,
    /// Controls whether `assert_zero[_ef]` / `assert_zero_linear` accumulate or just
    /// bump `constraint_index`. See [`FolderMode`].
    pub mode: FolderMode,
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
            skip_low: false,
            accumulator_low: EFPacking::<EF>::ZERO,
            cached_state: None,
            low_ci_count: 0,
            mode: FolderMode::All,
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
    fn bus_only(&self) -> bool {
        matches!(self.mode, FolderMode::BusOnly)
    }

    #[inline]
    fn assert_zero(&mut self, x: IF) {
        // BusOnly: only the first 2 alpha slots (multiplicity at 0, fingerprint at 1)
        // are accumulated — those are the bus. Later assertions inside the AIR
        // (e.g. poseidon's full rounds before the block, partial-round S-boxes) get
        // their `constraint_index` bumped but no accumulator update.
        let acc = match self.mode {
            FolderMode::All | FolderMode::HighOnly => true,
            FolderMode::BusOnly => self.constraint_index < 2,
            FolderMode::LinearOnly => false,
        };
        if acc {
            let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
            self.accumulator += EFPacking::<EF>::from(alpha_power) * x;
        }
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_ef(&mut self, x: EFPacking<EF>) {
        let acc = match self.mode {
            FolderMode::All | FolderMode::HighOnly => true,
            FolderMode::BusOnly => self.constraint_index < 2,
            FolderMode::LinearOnly => false,
        };
        if acc {
            let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
            self.accumulator += EFPacking::<EF>::from(alpha_power) * x;
        }
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_linear(&mut self, x: IF) {
        if matches!(self.mode, FolderMode::All | FolderMode::LinearOnly) {
            let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
            self.accumulator += EFPacking::<EF>::from(alpha_power) * x;
        }
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_eq_low(&mut self, x: IF, y: IF) {
        if matches!(self.mode, FolderMode::All | FolderMode::HighOnly) {
            let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
            let contrib = EFPacking::<EF>::from(alpha_power) * (x - y);
            self.accumulator += contrib;
            self.accumulator_low += contrib;
        }
        self.constraint_index += 1;
    }

    #[inline]
    fn low_degree_block<F>(&mut self, state: &mut [IF], block: F)
    where
        F: FnOnce(&mut Self, &mut [IF]),
    {
        // In `LinearOnly` mode the block contains no linear constraints, so skip it
        // entirely. In `BusOnly` mode we DO run the block (poseidon's degree-split
        // path needs the post-block state cached) — assertions inside are no-ops.
        if matches!(self.mode, FolderMode::LinearOnly) {
            self.constraint_index += self.low_ci_count;
            return;
        }
        if self.skip_low {
            state.copy_from_slice(self.cached_state.as_ref().unwrap());
            self.constraint_index += self.low_ci_count;
        } else {
            block(self, state);
            if let Some(cache) = &mut self.cached_state {
                cache.clear();
                cache.extend_from_slice(state);
            }
        }
    }
}
