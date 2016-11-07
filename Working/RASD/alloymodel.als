module PowerEnjoy

/**Classes**/

abstract sig Person {}

one sig Company {
		cars : set Car,
		chargingStations : set ChargingStation,
		users : set User,
		supportOperators : set SupportOperator
}

sig ChargingStation {
		capacity: set Plug,
		chargingCars : set Car
}{#chargingCars <= #capacity}

sig Plug{}

/**Actors**/

sig Guest  extends Person {}

sig User extends Person {
	  status : one Bool,
	  requests : set Request,
	  usingCar : lone Car
}

sig SupportOperator extends Person {
		isWorking : one Bool,
		isAvailable : one Bool
}{isAvailable = True implies isWorking = True}

sig Car {
		status : one CarStatus,
		inCharge : one Bool,
		isLocked : one Bool,
		userDriver : lone User
}{inCharge = True implies (status != CarInUse and isLocked = True)}

abstract sig CarStatus{}

lone sig CarAvailable extends CarStatus {}
lone sig CarNotAvailable extends CarStatus {}
lone sig CarReserved extends CarStatus {}
lone sig CarInUse extends CarStatus {}

/** Request **/

abstract sig Request {
		status: one Bool
}

sig ReservationRequest extends Request {}
sig UnlockRequest extends Request {}
sig LockRequest extends Request {}
sig LoginRequest extends Request {}
sig SignUpRequest extends Request {}
sig ChangePersonalInformation extends Request {}

/** Ride **/

abstract sig Ride {
		driver: one User,
		passengers : some Person,
		safeMode : one Bool
}{driver != none}

sig NormalRide extends Ride {} {#passengers <2 }
sig SharedRide extends Ride {} {#passengers >=2}
sig SafeModeRide extends Ride {} {safeMode = True}

/** Facts **/

fact allusersFit {
		all r: Ride | #r.passengers <= 4
}

fact rideHasReasonToExist {
		no r: Ride | r.user != none
}

/** Functions **/

/** Predicates **/

pred isCarAvailable [c : Car] {
		some s: CarAvailable | c.status in s
}

pred isCarInCharge [c: Car] {
		c.inCharge = True
}

pred isCarNotAvailable [c : Car] {
		some s: CarNotAvailable | c.status in s
}

pred isCarInUse [c : Car] {
		some s: CarInUse | c.status in s
}

pred isCarReserved [c : Car] {
		some s: CarReserved | c.status in s
}

pred isSupportOperatorAvailable [o : SupportOperator] {
		o.isAvailable = True
}

pred isSupportOperatorBusy [o : SupportOperator] {
		o.isAvailanble = False
}

pred isSupportOperatorWorking [o : SupportOperator]{
		o.isWorking = True
}

pred isActive [ u: User]{
		u.status = True
}

pred isRequestApproved [r: Request]{
		r.status = True
}





