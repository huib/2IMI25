using CP;

// Define tuples for data import

tuple Character {
	key string name;
	string type;
}

tuple Scene {
  key string nameAct;
  {string} names;
}

// Import the data
{string} CharacterTypes = ...;
{Character} Characters = ...;

{string} LeadingCharacters = ...;
int maxNrOfCharacters = ...;
{Scene} Scenes = ...;

// Set the settings
execute {
	cp.param.Workers = 1;
	cp.param.TimeLimit = 5; 
}

// Keep the 
dvar int actorPlaysInScene[c in Characters][s in Scenes];

// As said, we are looking for an assignment of actors to characters that satisfies the 
// above given constraints and that minimizes the number of required actors.
dvar int NrOfActorsNeeded;
minimize NrOfActorsNeeded;

// Add the constraints
subject to {
	// TODO
	
	// Once an actor plays a certain character in a scene for example, he or she needs
	// to play that character in the whole play. 
	
	// Another constraint is that you cannot have two actors together play a character 
	// as that will confuse the audience. 
	
	// An actor obviously also cannot play more than one character in the same scene. 
	
	// There are furthermore a couple of leading characters and the actors assigned to 
	// those characters cannot play any other character as that would again confuse the 
	// audience. 
	
	// There are also parts for males that can only be played by men, parts for females
	// that can only be played by women, etc. 
	
	// Another constraint is that to allow people to change costume, an actor cannot play
	// one character in one scene and another in the scene that is directly next, i.e., 
	// at least one scene needs to be in between any actor playing two different characters.
	
	// A final constraint is that no actor can be assigned to more than a given maximal
	// number of characters, this as assigning too many characters to an actor will again 
	// confuse the audience.
	
	// DONE
	// Maintain actorsNeeded
	forall(c in Characters)
	  forall(s in Scenes)
	    actorPlaysInScene[c][s] >= 0;
	    
    NrOfActorsNeeded == max(c in Characters, s in Scenes) actorPlaysInScene[c][s];
}

int nrOfActorsOfType[ct in CharacterTypes];
{Character} CharactersPlayedByActor[i in 0..NrOfActorsNeeded-1];

// Give the desired output
execute {
  	writeln("Actors needed: ", NrOfActorsNeeded);
  	
  	for(var ct in CharacterTypes) {
  		writeln(ct, " needed: ", nrOfActorsOfType[ct]);
   	}  	  
   			     	
  	for(var i=0; i<NrOfActorsNeeded; i++) {
  	  writeln("Actor ", i, " plays ", CharactersPlayedByActor[i]);
    }  	  
}
