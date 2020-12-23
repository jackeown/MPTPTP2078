%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:26 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   59 (  59 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u147,negated_conjecture,(
    k13_lattice3(sK0,sK4,sK5) != k13_lattice3(sK1,sK4,sK5) )).

tff(u146,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),sK4,X0) = k1_enumset1(sK4,sK4,X0) )
    | k7_domain_1(u1_struct_0(sK0),sK4,sK4) = k1_enumset1(sK4,sK4,sK4) )).

tff(u145,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),sK4,X0) = k1_enumset1(sK4,sK4,X0) )
    | k7_domain_1(u1_struct_0(sK0),sK4,sK5) = k1_enumset1(sK4,sK4,sK5) )).

tff(u144,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),sK5,X1) = k1_enumset1(sK5,sK5,X1) )
    | k7_domain_1(u1_struct_0(sK0),sK5,sK4) = k1_enumset1(sK5,sK5,sK4) )).

tff(u143,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),sK5,X1) = k1_enumset1(sK5,sK5,X1) )
    | k7_domain_1(u1_struct_0(sK0),sK5,sK5) = k1_enumset1(sK5,sK5,sK5) )).

tff(u142,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),sK5,X2) = k1_enumset1(sK5,sK5,X2) )
    | k1_enumset1(sK5,sK5,sK5) = k7_domain_1(u1_struct_0(sK1),sK5,sK5) )).

tff(u141,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),sK5,X2) = k1_enumset1(sK5,sK5,X2) )
    | k1_enumset1(sK5,sK5,sK4) = k7_domain_1(u1_struct_0(sK1),sK5,sK4) )).

tff(u140,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | k7_domain_1(X0,X1,X2) = k1_enumset1(X1,X1,X2)
      | v1_xboole_0(X0) ) )).

tff(u139,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),sK5,X1) = k1_enumset1(sK5,sK5,X1) )
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),sK5,X1) = k1_enumset1(sK5,sK5,X1) ) )).

tff(u138,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),sK4,X0) = k1_enumset1(sK4,sK4,X0) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),sK4,X0) = k1_enumset1(sK4,sK4,X0) ) )).

tff(u137,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK1))
          | k7_domain_1(u1_struct_0(sK1),sK5,X2) = k1_enumset1(sK5,sK5,X2) )
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | k7_domain_1(u1_struct_0(sK1),sK5,X2) = k1_enumset1(sK5,sK5,X2) ) )).

tff(u136,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK0)) )).

tff(u135,negated_conjecture,(
    m1_subset_1(sK5,u1_struct_0(sK0)) )).

tff(u134,negated_conjecture,(
    m1_subset_1(sK5,u1_struct_0(sK1)) )).

tff(u133,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK1)) )).

tff(u132,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u131,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u130,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

tff(u129,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u128,axiom,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u127,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u126,negated_conjecture,
    ( ~ ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK1) )).

tff(u125,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u124,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u123,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u122,negated_conjecture,(
    v1_lattice3(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:41:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (23378)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (23380)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (23380)Refutation not found, incomplete strategy% (23380)------------------------------
% 0.21/0.46  % (23380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23385)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (23377)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (23379)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (23390)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (23379)# SZS output start Saturation.
% 0.21/0.47  tff(u147,negated_conjecture,
% 0.21/0.47      (k13_lattice3(sK0,sK4,sK5) != k13_lattice3(sK1,sK4,sK5))).
% 0.21/0.47  
% 0.21/0.47  tff(u146,negated_conjecture,
% 0.21/0.47      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK4,X0) = k1_enumset1(sK4,sK4,X0)))))) | (k7_domain_1(u1_struct_0(sK0),sK4,sK4) = k1_enumset1(sK4,sK4,sK4)))).
% 0.21/0.47  
% 0.21/0.47  tff(u145,negated_conjecture,
% 0.21/0.47      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK4,X0) = k1_enumset1(sK4,sK4,X0)))))) | (k7_domain_1(u1_struct_0(sK0),sK4,sK5) = k1_enumset1(sK4,sK4,sK5)))).
% 0.21/0.47  
% 0.21/0.47  tff(u144,negated_conjecture,
% 0.21/0.47      ((~(![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK5,X1) = k1_enumset1(sK5,sK5,X1)))))) | (k7_domain_1(u1_struct_0(sK0),sK5,sK4) = k1_enumset1(sK5,sK5,sK4)))).
% 0.21/0.47  
% 0.21/0.47  tff(u143,negated_conjecture,
% 0.21/0.47      ((~(![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK5,X1) = k1_enumset1(sK5,sK5,X1)))))) | (k7_domain_1(u1_struct_0(sK0),sK5,sK5) = k1_enumset1(sK5,sK5,sK5)))).
% 0.21/0.47  
% 0.21/0.47  tff(u142,negated_conjecture,
% 0.21/0.47      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),sK5,X2) = k1_enumset1(sK5,sK5,X2)))))) | (k1_enumset1(sK5,sK5,sK5) = k7_domain_1(u1_struct_0(sK1),sK5,sK5)))).
% 0.21/0.47  
% 0.21/0.47  tff(u141,negated_conjecture,
% 0.21/0.47      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),sK5,X2) = k1_enumset1(sK5,sK5,X2)))))) | (k1_enumset1(sK5,sK5,sK4) = k7_domain_1(u1_struct_0(sK1),sK5,sK4)))).
% 0.21/0.47  
% 0.21/0.47  tff(u140,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | (k7_domain_1(X0,X1,X2) = k1_enumset1(X1,X1,X2)) | v1_xboole_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u139,negated_conjecture,
% 0.21/0.47      ((~(![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK5,X1) = k1_enumset1(sK5,sK5,X1)))))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK5,X1) = k1_enumset1(sK5,sK5,X1))))))).
% 0.21/0.47  
% 0.21/0.47  tff(u138,negated_conjecture,
% 0.21/0.47      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK4,X0) = k1_enumset1(sK4,sK4,X0)))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK4,X0) = k1_enumset1(sK4,sK4,X0))))))).
% 0.21/0.47  
% 0.21/0.47  tff(u137,negated_conjecture,
% 0.21/0.47      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),sK5,X2) = k1_enumset1(sK5,sK5,X2)))))) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),sK5,X2) = k1_enumset1(sK5,sK5,X2))))))).
% 0.21/0.47  
% 0.21/0.47  tff(u136,negated_conjecture,
% 0.21/0.47      m1_subset_1(sK4,u1_struct_0(sK0))).
% 0.21/0.47  
% 0.21/0.47  tff(u135,negated_conjecture,
% 0.21/0.47      m1_subset_1(sK5,u1_struct_0(sK0))).
% 0.21/0.47  
% 0.21/0.47  tff(u134,negated_conjecture,
% 0.21/0.47      m1_subset_1(sK5,u1_struct_0(sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u133,negated_conjecture,
% 0.21/0.47      m1_subset_1(sK4,u1_struct_0(sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u132,axiom,
% 0.21/0.47      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u131,negated_conjecture,
% 0.21/0.47      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u130,negated_conjecture,
% 0.21/0.47      ((~v1_xboole_0(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK1)))).
% 0.21/0.47  
% 0.21/0.47  tff(u129,negated_conjecture,
% 0.21/0.47      ~v2_struct_0(sK1)).
% 0.21/0.47  
% 0.21/0.47  tff(u128,axiom,
% 0.21/0.47      (![X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u127,negated_conjecture,
% 0.21/0.47      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.21/0.47  
% 0.21/0.47  tff(u126,negated_conjecture,
% 0.21/0.47      ((~~l1_struct_0(sK1)) | ~l1_struct_0(sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u125,negated_conjecture,
% 0.21/0.47      l1_struct_0(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u124,axiom,
% 0.21/0.47      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u123,negated_conjecture,
% 0.21/0.47      l1_orders_2(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u122,negated_conjecture,
% 0.21/0.47      v1_lattice3(sK0)).
% 0.21/0.47  
% 0.21/0.47  % (23379)# SZS output end Saturation.
% 0.21/0.47  % (23379)------------------------------
% 0.21/0.47  % (23379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23379)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (23379)Memory used [KB]: 6140
% 0.21/0.47  % (23379)Time elapsed: 0.062 s
% 0.21/0.47  % (23379)------------------------------
% 0.21/0.47  % (23379)------------------------------
% 0.21/0.47  % (23376)Success in time 0.114 s
%------------------------------------------------------------------------------
