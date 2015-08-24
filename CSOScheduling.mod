#########################################
#  CSO Scheduling Model
#########################################

set people;       # CSO's
set shifts;       # A contiguous block of time with one type of person working
set timeSlots;    # We discritise time into 24 * 7 * 4 chunks throughout the week

# How many timeSlots are in an hour?
param timeSlotsPerHour >= 0;

# What limitations does each person have on their work?
param isOIC{people} >= 0;
param isDispatch{people} >= 0;
param isSIO{people} >= 0;
param isTrainee{people} >= 0;
param isAvailable{people, timeSlots} >= 0;

# max hours you want to work
param targetHours{people} >= 0;
# maximum number of hours anyone can work
param maxHours >= 0;

# When is a shift running, and who needs to work it?
param isRunning{shifts, timeSlots} >= 0;
param numPeople{shifts} >= 0;
param numOIC{shifts} >= 0;
param numSIO{shifts} >= 0;
param numDispatch{shifts} >= 0;
param maxNumTrainees{shifts} >= 0;

# 1 if this person is working this shift, 0 otherwise
var isWorkingShift{people, shifts} binary;
# 1 if this person is working during this time slot, 0 otherwise
var isWorkingTime{people, timeSlots} binary;

# for printing
var numPeopleWorkingToPrint{shifts};


# Objective: find a valid schedule (this objective fn currently does nothing)
minimize nothing:
	1;

# Per shift, exactly the right number of people work
subject to numPeopleWorking{s in shifts}:
	numPeople[s] = numPeopleWorkingToPrint[s];

subject to numPeopleWorkingToPrintConstraint{s in shifts}:
	numPeopleWorkingToPrint[s] = sum{p in people} isWorkingShift[p, s];

# Per shift, at least as many OICs work as necessary
subject to numOICWorking{s in shifts}:
	numOIC[s] <= sum{p in people} (isWorkingShift[p, s] * isOIC[p]);

# At least as many dispatchers work as needed
subject to numDispatchWorking{s in shifts}:
	numDispatch[s] <= sum{p in people} (isWorkingShift[p, s] * isDispatch[p]);

# At least as many SIO as needed
subject to numSIOWorking{s in shifts}:
	numSIO[s] <= sum{p in people} (isWorkingShift[p, s] * isSIO[p]);

# No more than the maximum number of trainees
subject to maxNumTraineesWorking{s in shifts}:
	maxNumTrainees[s] >= sum{p in people} (isWorkingShift[p, s] * isTrainee[p]);

# You can't work during a time slot if you're not available
subject to mustBeAvailableDuringSlot{p in people, t in timeSlots}:
	isAvailable[p, t] >= isWorkingTime[p, t];

# If you're working a shift, you must be available
subject to mustBeAvailableForShift{p in people, s in shifts, t in timeSlots}:
	isWorkingShift[p, s] * isRunning[s, t] <= isAvailable[p, t];

# If you're not working any shifts during a give time slot, you're not
# working during that time slot (enforces link between workingTime and
# workingShift)
subject to linkWorkWithShift{p in people, t in timeSlots}:
	isWorkingTime[p, t] <= sum{s in shifts} (isWorkingShift[p, s] * isRunning[s, t]);

# If you're working shift s, you're working during all of its hours
subject to workingEntireShift{p in people, s in shifts, t in timeSlots}:
	isWorkingShift[p, s] * isRunning[s, t] <= isWorkingTime[p, t];

# You can't work more than one shift at a time
subject to oneShiftAtATime{p in people, t in timeSlots}:
	sum{s in shifts} (isWorkingShift[p, s] * isRunning[s, t]) <= 1;

# No one can go over the maximum number of hours
subject to maxHoursConstraint{p in people}:
	sum{t in timeSlots} isWorkingTime[p, t] <= maxHours * timeSlotsPerHour;

# You can't go over your preferred number of hours
subject to individualHourPreferences{p in people}:
	sum{t in timeSlots} isWorkingTime[p, t] <= targetHours[p] * timeSlotsPerHour;



