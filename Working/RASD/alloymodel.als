module PowerEnjoy
open util/boolean

/**Classes**/

abstract sig Person {}

one sig Company {
		cars : set Car,
		chargingStations : set ChargingStation,
		users : set User,
		supportOperators : set SupportOperator,
		safeAreas : set Position
}

sig Position{}

sig ChargingStation {
		capacity: set Plug,
		chargingCars : set Car
}{#chargingCars <= #capacity}

sig Plug{}

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
		isLocked : one Bool,
		position : one Position,
		userDriver : lone User,
		company : one Company,
		batteryLevel : one Int,
}{(inCharge = True implies (status != CarInUse and isLocked = True))
	and isLocked = True implies status != CarInUse}

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
	sig totalDiscount { 
		value : Int 
}

/**fun applyDiscounts [r : Ride] : Ride {
		#r.passengers >= 2 => (totalDiscount.value = mul[10,div[r.actualFee,100]]) 
		r.car.batteryLevel >= 50 => (totalDiscount.value = plus[totalDiscount.value, mul[20, div[r.actualFee,100]]]) 
		r.car.inCharge = True => (totalDiscount.value = plus[totalDiscount.value, mul[30, div[r.actualFee,100]]]) 
		r.car.batteryLevel < 20 => (totalDiscount.value = sub[totalDiscount.value, mul[30, div[r.actualFee,100]]]) 
		r.car.actualFee = sub[r.car.actualFee, totalDiscount.value]
		totalDiscount = 0
		this
} CHIEDERE ALLA PROF **/
		

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

pred carCanPark [c: Car] {
		c.position in c.company.safeAreas
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

pred showGeneral {
		#NormalRide = 1
		#SharedRide = 1
		#User = 5
		#Car > #User
		#Company = 1
}

run showGeneral for 5





