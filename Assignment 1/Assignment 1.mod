using CP;

// Define tuples for data import
tuple CharacterType {
	key string type;
}

tuple Character {
	key string name;
	CharacterType type;
}

tuple Scene {
  key string nameAct;
  {string} names;
}

// Import the data
{CharacterType} CharacterTypes = ...;
{Character} Characters = ...;

{Character} LeadingCharacters = ...;
int maxNrOfCharacters = ...;
{Scene} Scenes = ...;

// Set the settings
execute {
	cp.param.Workers = 1;
	cp.param.TimeLimit = 5; 
}

// Add the constraints
subject to {
	// TODO
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