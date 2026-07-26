use field::{HasExtensionPacking, HasPacking, PrimeCharacteristicRing};

pub type PF<F> = <F as PrimeCharacteristicRing>::PrimeSubfield;
pub type FPacking<F> = <F as HasPacking>::Packing;
pub type PFPacking<F> = <PF<F> as HasPacking>::Packing;
pub type EFPacking<EF> = <EF as HasExtensionPacking<PF<EF>>>::ExtensionPacking;

pub use koala_bear::{KoalaBearExtension, KoalaBearExtensionNoPacking};
