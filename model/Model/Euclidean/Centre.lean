module

public import Model.Euclidean
public import Model.Hand

/-!
# Every circle has a centre, in the plane

The law proposed in issue #59, proved in the model before it lands in the library. In the
plane it is immediate: a circle is read as a sphere, and a sphere carries its centre.
-/

@[expose] public section

namespace Model.Euclidean

/-- **The proposed `exists_centre` holds in the plane:** the centre of the circle α is the
centre of the sphere that α is read as. -/
theorem exists_centre : Hand.exists_centre plane :=
  fun α => ⟨α.1.center, rfl⟩

end Model.Euclidean
