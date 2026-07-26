use field::{ExtensionField, Field, HasExtensionPacking, HasPacking, PrimeCharacteristicRing};

use crate::KoalaBear;

/// `KoalaBearExtension` minus the SIMD packing requirements.
///
/// Verifier code uses this so that extraction never reaches `HasPacking` /
/// `HasExtensionPacking`, whose associated types Charon cannot lift (their bounds mention `Self`).
pub trait KoalaBearExtensionNoPacking:
    Field + ExtensionField<KoalaBear> + PrimeCharacteristicRing<PrimeSubfield = KoalaBear>
{
}

impl<T: Field + ExtensionField<KoalaBear> + PrimeCharacteristicRing<PrimeSubfield = KoalaBear>>
    KoalaBearExtensionNoPacking for T
{
}

pub trait KoalaBearExtension: KoalaBearExtensionNoPacking + HasPacking + HasExtensionPacking<KoalaBear> {}

impl<T: KoalaBearExtensionNoPacking + HasPacking + HasExtensionPacking<KoalaBear>> KoalaBearExtension for T {}
