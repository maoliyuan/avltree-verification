pragma solidity >=0.4.22 <0.6.0;

contract TradeSystem {
    /* This creates an array with all balances */
    mapping (address => uint256) public balanceOf;
    mapping (address => uint256) public stocks;
    event Sell(address from, uint price, uint amount);
    event Buy(address from, uint price, uint amount);
    
    bool private constant RED   = false;
    bool private constant BLACK = true;
    
    bool private constant SELL =false;
    bool private constant BUY =true;
    
    bool private constant LEFT =false;
    bool private constant RIGHT =true;
    struct  node 
    {
        uint256 key; /* that is price*/
        uint s_value; /* sell amount */
        uint b_value; /* buy value */
        uint s_delta; /* sell delta */
        uint b_delta; /* buy delta*/
        bool  color;
        uint256  left;  // 0 : no left child 
        uint256  right;  // 0 : no right child 
        uint256  parent;
    }
    
    struct  RBtree
    {
        mapping(uint => node) entries;
        uint nodesLength;
        // index of the root 
        uint rootIdx; // 0 presents this is an empty tree
    }
    
    RBtree PriceTree;
    
    /* Initializes contract with initial supply tokens to the creator of the contract */
    constructor(
        uint256 initialSupply, uint256 initialstock
        ) public {
        balanceOf[msg.sender] = initialSupply;
        stocks[msg.sender]=initialstock;
        PriceTree.nodesLength=0;
        PriceTree.rootIdx=0;
        // Give the creator all initial tokens
    }
    /* some  functions  which cannot be called by orders
      So how to set these functions ? */
      
    /* this function creates a node and return the index i.e. pointer and the node */
    function _createNode( uint _key, uint _value , bool  _s_or_b) internal returns(uint index, node storage newnode)
    { 
        // protects from index overflow
        if (PriceTree.nodesLength == 2**256 - 1) {
        revert("uint overflow: unable insert more prices");
        }

        index = ++PriceTree.nodesLength;
        uint b_v=0;
        uint s_v=0;
        if (_s_or_b ) b_v = _value ;
        else s_v==_value;
        PriceTree.entries[index] = node(
            _key,
            s_v,
            b_v, 
            0,0, // delta initializes to be 0 
            RED, 
            0,0,0 // None
        );

    newnode = PriceTree.entries[index];
     }
     
    /*  set root node to BLACK color */
    function _setRootToBlack()
    internal
    {
        PriceTree.entries[PriceTree.rootIdx].color = BLACK;
    }
    /* this function will rotate the subtree with _o_root to be the center */
    function _rotate (uint _o_root, bool _direction) public returns (bool success) { 
        // rotate right 
        if (_direction){
            uint pa = PriceTree.entries[_o_root].parent;
            
            uint new_root = PriceTree.entries[_o_root].left;
            require (new_root > 0);
            uint b = PriceTree.entries[new_root].right;
            
            // _o_root is the root
            if (pa == 0 ) PriceTree.rootIdx=new_root;
            else {
                if (PriceTree.entries[pa].key < PriceTree.entries[_o_root].key)
                PriceTree.entries[pa].right = new_root;
                else PriceTree.entries[pa].left = new_root;}
                
            PriceTree.entries[new_root].right = _o_root;
            PriceTree.entries[_o_root].left = b;
            //fix up
            PriceTree.entries[_o_root].s_value -= PriceTree.entries[new_root].s_value;
            PriceTree.entries[_o_root].s_delta -= PriceTree.entries[new_root].s_delta;
                
            PriceTree.entries[new_root].b_value += PriceTree.entries[_o_root].b_value;
            PriceTree.entries[new_root].b_delta += PriceTree.entries[_o_root].b_delta;
            
        }
        // rotate left
        else {
            uint pa = PriceTree.entries[_o_root].parent;
            
            uint new_root = PriceTree.entries[_o_root].right;
            require (new_root > 0);
            uint b = PriceTree.entries[new_root].left;
            
            // _o_root is the root
            if (pa == 0 ) PriceTree.rootIdx=new_root;
            else {
                if (PriceTree.entries[pa].key < PriceTree.entries[_o_root].key)
                PriceTree.entries[pa].right = new_root;
                else PriceTree.entries[pa].left = new_root;}
                
            PriceTree.entries[new_root].left = _o_root;
            PriceTree.entries[_o_root].right = b;
            //fix up
            PriceTree.entries[_o_root].b_value -= PriceTree.entries[new_root].b_value;
            PriceTree.entries[_o_root].b_delta -= PriceTree.entries[new_root].b_delta;
                
            PriceTree.entries[new_root].s_value += PriceTree.entries[_o_root].s_value;
            PriceTree.entries[new_root].s_delta += PriceTree.entries[_o_root].s_delta;
            
            
        }
    }
    
    function _RB_fixup (uint _index) public returns (bool success) {
         uint pa = PriceTree.entries[_index].parent;
         
         // the new node is the root
         if (pa ==0 ) {  _setRootToBlack(); return true;}
         // the new node's parent's color is black, this node's color is red , and the RBtree Properties still hold
         if (PriceTree.entries[pa].color) return true;
         
         // the following cases : the parent color is red.
         // So the grandparent must be black and it must have grandparent
         // that is greanpa != 0 
         uint grandpa = PriceTree.entries[pa].parent;
         // pa_direction : true ie. right , otherwise left
         bool pa_direction =  PriceTree.entries[grandpa].key < PriceTree.entries[pa].key ? RIGHT : LEFT;
         // uncle is the grandpa node's another child
         uint uncle;
         if (pa_direction)  uncle = PriceTree.entries[grandpa].left;
         else uncle = PriceTree.entries[grandpa].right;
         bool current_direction =  PriceTree.entries[grandpa].key < PriceTree.entries[pa].key ? RIGHT : LEFT;
         
         // pa is grandpa'right child
         if (pa_direction){
             // case 1 : uncle's color is red
            if (uncle != 0 && (! PriceTree.entries[uncle].color) ) {
                 PriceTree.entries[pa].color = BLACK ;
                 PriceTree.entries[uncle].color =BLACK;
                 PriceTree.entries[grandpa].color = RED;
                 return _RB_fixup(grandpa);
            }
            
            // case 2: no uncle or uncle's color is black  && this node is pa'right child 
            else if (current_direction)
            {
                PriceTree.entries[pa].color=BLACK;
                PriceTree.entries[grandpa].color=RED;
                _rotate(grandpa, LEFT);
                return _RB_fixup(grandpa);
            }
              // case 2: no uncle or uncle's color is black  && this node is pa'left child 
            else {
                 _rotate(pa,RIGHT);
                 return _RB_fixup(pa);
            }
         }
         
         // pa is grandpa'left child
         else {
            
            // case 1 : uncle's color is red
            if (uncle != 0 && (! PriceTree.entries[uncle].color) ) {
                 PriceTree.entries[pa].color = BLACK ;
                 PriceTree.entries[uncle].color =BLACK;
                 PriceTree.entries[grandpa].color = RED;
                 return _RB_fixup(grandpa);
            }
            
            // case 2: no uncle or uncle's color is black  && this node is pa'right child 
            else if (current_direction)
            {
                _rotate(pa, LEFT);
                return _RB_fixup(pa);
            }
              // case 2: no uncle or uncle's color is black  && this node is pa'left child 
            else {
                 PriceTree.entries[grandpa].color=RED;
                 PriceTree.entries[pa].color=BLACK;
                 _rotate(grandpa,RIGHT);
                 return _RB_fixup(grandpa);
            }
         
         } 
     }
    // for a price, find the how many customers want to buy and sell
    function _query_price (uint _price) public returns (uint _buy_amount, uint _sell_amount) {
        _buy_amount =0;
        _sell_amount =0;
        uint current_node = PriceTree.rootIdx;
        uint current_key = PriceTree.entries[current_node].key;
        while (_price != current_key ) {
            if (current_key > _price) {
                _buy_amount += PriceTree.entries[current_node].b_value;
                _buy_amount += PriceTree.entries[current_node].b_delta;
                current_node = PriceTree.entries[current_node].left;
                if (current_node == 0) break; 
                current_key = PriceTree.entries[current_node].key;
            }
            else {
                _sell_amount += PriceTree.entries[current_node].s_value;
                _sell_amount += PriceTree.entries[current_node].s_delta;
                current_node = PriceTree.entries[current_node].left;
                if (current_node == 0) break; 
                current_key = PriceTree.entries[current_node].key;
            }
        }
        
        if (current_node !=0) {
            _buy_amount += PriceTree.entries[current_node].b_value;
            _buy_amount += PriceTree.entries[current_node].b_delta;
            _sell_amount += PriceTree.entries[current_node].s_value;
            _sell_amount += PriceTree.entries[current_node].s_delta;
        }
        }
        
     // functoin :     how to get the balance node ???? 
     function _get_balance_node () public returns (uint _price, uint _buy_amount, uint _sell_amount) {
        _buy_amount = 0; 
        _sell_amount = 0;
        uint current_node = PriceTree.rootIdx;
        uint current_key = PriceTree.entries[current_node].key;
        // if the tree is an empty tree
        if (current_node == 0) _price =0;
        else 
            while (current_node != 0) {
                _price = PriceTree.entries[current_node].key;
                _buy_amount += PriceTree.entries[current_node].b_value;
                _buy_amount += PriceTree.entries[current_node].b_delta;
                _sell_amount += PriceTree.entries[current_node].s_value;
                _sell_amount += PriceTree.entries[current_node].s_delta;
                if (_buy_amount == _sell_amount ) break; 
                if (_buy_amount > _sell_amount) 
                    current_node = PriceTree.entries[current_node].right;
                   
                if (_buy_amount < _sell_amount) 
                    current_node = PriceTree.entries[current_node].left;
            }
     }
        
 
        
        
    function _segment_fixup (uint _index, uint _price, uint _amount , bool _s_or_b) public returns (bool success) 
    {
        uint pa = PriceTree.entries[_index].parent;
        // case 1 : it's the root 
        if (pa== 0) return true;
        
    
        // fix up the buy line 
        if (_s_or_b ){
            // find the first node whose key is less than _price 
            while (PriceTree.entries[pa].key  > _price ) {
                pa= PriceTree.entries[pa].parent;
                if (pa == 0) break;
            }
            if (pa == 0 ) return true; // no node whos key is less than _price . ie  this node'insert has no influence on other nodes.
            
            // in this case , PriceTree.entris[pa].key < _price (it is impossible that they will be equal)
            PriceTree.entries[pa].b_delta += _amount;
            // the node pa has changed ,so we should consider its influence
            return _segment_fixup (pa, _price, _amount , _s_or_b );
        }
        else {
            // find the first node whose key is large than _price
            while (PriceTree.entries[pa].key < _price) {
                pa= PriceTree.entries[pa].parent;
                if (pa == 0 )break;
            }
            if (pa == 0 ) return true; // no node whos key is large than _price . ie  this node'insert has no influence on other nodes.
             
            // in this case , PriceTree.entris[pa].key > _price (it is impossible that they will be equal)
            PriceTree.entries[pa].s_delta += _amount;
            // the node pa has changed ,so we should consider its influence
            return _segment_fixup (pa, _price, _amount , _s_or_b );
        }
        
        return true;
    }
    function _insert_node (uint _price, uint _amount , bool _s_or_b ) public returns (bool success)
    {
        uint  index ;
        node  memory newnode; /* ? */
        (index , newnode) = _createNode(_price , _amount , _s_or_b);
		if (PriceTree.rootIdx == 0) {
		  // insert into an empty tree
		  PriceTree.rootIdx=index;
		}
		else {
		  bool exact = false; /* 1: not a new price */
		  uint c = PriceTree.rootIdx; /* currentIdx*/
		  uint pa = 0; /* parentIdx*/
		  // find where to insert this price node 
		  while (c !=0 ) {
		      if ( PriceTree.entries[c].key == _price ) { exact =true;  break; } 
              else if ( PriceTree.entries[c].key > _price  ) {
			      pa = c;
				  c = PriceTree.entries[pa].left;
			  }	
              else 	{
			      pa = c;
                  c = PriceTree.entries[pa].right;				  
			  }		  
		  }
		  if (exact) {
		      if (_s_or_b ) PriceTree.entries[c].b_value+=_amount;
		      else PriceTree.entries[c].s_value+=_amount;
		      _segment_fixup(c, _price, _amount,_s_or_b);
		  }
		  else if (PriceTree.entries[pa].key > _price  ) { 
		      PriceTree.entries[pa].left = index;
		      _segment_fixup(index, _price, _amount , _s_or_b);
		      /*  NOT FINISHED */
		  }
		  else {
		      PriceTree.entries[pa].right = index;
		      _segment_fixup(index , _price , _amount ,_s_or_b);
		      /*  NOT FINISHED */
		  }
		  
		}
        return true;
    }
    /* Sell price amount */
    function _sell_order(uint _price, uint256 _amount) public returns (bool success) {
        require (stocks[msg.sender] >= _amount);  // Check if the sender has enough
        _insert_node(_price,_amount, SELL); // update RBtree
        emit Sell (msg.sender, _price,_amount) ; //show the events
        
        /* NOT FINISHED */
        return true;
    }
    function _buy_order(uint _price, uint256 _amount) public returns (bool success) {
        require(balanceOf[msg.sender] >= _price * _amount);     // Check if the sender has enough
        _insert_node(_price,_amount, BUY); // update RBtree
        emit Buy (msg.sender, _price,_amount) ; //show the events
        
        /* NOT FINISHED */
        return true;
    }
    
    
}
