record Entry {
       int key;
       Entry next;
       boolean marked;
       Mutex lck;
}

const unique null: Entry;

const unique Head: Entry;
const unique Tail: Entry;


procedure lookup(key: int) returns (prev: Entry, curr: Entry)
{
	prev := Head;
	curr := Head.next;
	while(curr.key < key)
	{
		prev := curr;
		curr := curr.next;
	}
}

procedure add(key: int) returns (wasPresent: bool)
{
	var prev, curr: Entry;

	call prev, curr := lookup(key);

	call lock(prev.lck);
	call lock(curr.lck);
	if(prev.marked == False)
	{
		wasPresent = (curr.key != key);
		if(!wasPresent)
		{
			Entry tmp := new Entry;
			tmp.marked := False;
			tmp.key := key;
			tmp.next := curr;
			prev.next := tmp;
		}
	}
	call unlock(prev.lck);
	call unlock(curr.lck);
}

procedure remove(key: int) returns (wasPresent: bool)
{
	var prev, curr: Entry;

	call prev, curr := lookup(key);

	call lock(prev.lck);
	call lock(curr.lck);
	if(prev.marked == False)
	{
		wasPresent = (curr.key != key);
		if(wasPresent)
		{
			curr.marked := True;
			prev.next := curr.next;
		}
	}
	call unlock(prev.lck);
	call unlock(curr.lck);
}

procedure contains(key: int) returns (wasPresent: bool)
{
	var prev, curr: Entry;

	call prev, curr := lookup(key);

	wasPresent := (curr.key == key);
}