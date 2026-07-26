use field::{ExtensionField, Field, HasExtensionPacking, HasPacking, PrimeCharacteristicRing};

use crate::KoalaBear;

pub trait KoalaBearExtension:
    Field
    + ExtensionField<KoalaBear>
    + PrimeCharacteristicRing<PrimeSubfield = KoalaBear>
    + HasPacking
    + HasExtensionPacking<KoalaBear>
{
}

impl<
    T: Field
        + ExtensionField<KoalaBear>
        + PrimeCharacteristicRing<PrimeSubfield = KoalaBear>
        + HasPacking
        + HasExtensionPacking<KoalaBear>,
> KoalaBearExtension for T
{
}
