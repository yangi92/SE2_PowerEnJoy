module PowerEnjoy
open util/boolean

/**Classes**/

abstract sig Person {}


sig ChargingStation {
	
		chargingCars : set Car
}



/**Actors**/

sig Guest  extends Person {}

sig User extends Person {
	  username : one String,
	  statusConnected : one Bool,
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
	
	
		userDriver : lone User,
	
	
}

abstract sig CarStatus{}

lone sig CarAvailable extends CarStatus {}
lone sig CarNotAvailable extends CarStatus {}
lone sig CarReserved extends CarStatus {}
lone sig CarInUse extends CarStatus {}
lone sig CarLocked extends CarStatus{}

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
		car : one Car,
		passengers : some Person,
		safeMode : one Bool,
		actualFee : one Int
}{driver != none}

sig NormalRide extends Ride {} {#passengers <2 }
sig SharedRide extends Ride {} {#passengers >=2}
sig SafeModeRide extends Ride {} {safeMode = True}

/** Facts **/

fact userIsUnique {
		all u : User, u' : User | u != u' and u.username != u'.username
}

fact userDontUseSameCar {
		all u: User, u': User | u != u' and u.usingCar != none and u.usingCar != u'.usingCar 
}

fact allusersFit {
		all r: Ride | #r.passengers <= 4
}

fact rideHasReasonToExist {
		no r: Ride | (r.driver != none or r.car != none)
}

/** Functions **/




/** Predicates **/

pred isCarAvailable [c : Car] {
		some s: CarAvailable | c.status in s and c.status != CarLocked}

pred isCarInCharge [c: Car] {
		some c.inCharge implies c.status=CarNotAvailable
}

pred isCarNotAvailable [c : Car] {
		some s: CarNotAvailable | c.status in s
}

pred isCarInUse [c : Car] {
		some s: CarInUse| c.status in s
}

pred isCarReserved [c : Car] {
		some s: CarReserved | c.status in s
}


pred isUserConnected [u: User] {
		u.statusConnected = True
}

pred isSupportOperatorAvailable [o : SupportOperator] {
		o.isAvailable = True
}

pred isSupportOperatorBusy [o : SupportOperator] {
		o.isAvailable = False
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

pred show {
		
}

run show for 5 but 3 User, 5 Car





