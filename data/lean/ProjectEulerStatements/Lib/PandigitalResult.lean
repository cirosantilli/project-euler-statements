import ProjectEulerStatements.Lib.PandigitalReference
import ProjectEulerStatements.Lib.PandigitalCertificate

/-! Connect the arithmetic reduction and bounded kernel certificates. -/
namespace ProjectEulerStatements.PandigitalProducts

set_option Elab.async false

theorem reference_value : P32.naive 99 9999 = 45228 := by
  rw [PandigitalReference.naive_eq_referenceProducts]
  have checked : PandigitalReference.referenceProducts = PandigitalCertificate.productsFound := by
    simpa only [PandigitalReference.referenceProducts, PandigitalReference.referenceRow,
      PandigitalCertificate.referenceChunk] using PandigitalCertificate.reference_products
  rw [checked, PandigitalCertificate.answer]

theorem optimized_value : products.eraseDups.sum = 45228 := by
  rw [PandigitalCertificate.optimized_products, PandigitalCertificate.answer]

theorem equiv : products.eraseDups.sum = P32.naive 99 9999 := by
  rw [optimized_value, reference_value]

end ProjectEulerStatements.PandigitalProducts
