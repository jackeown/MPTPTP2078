%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:12 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u113,negated_conjecture,
    ( ~ ( sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u112,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) )).

tff(u111,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u110,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u109,axiom,
    ( ~ ! [X0] :
          ( ~ v1_xboole_0(u1_struct_0(X0))
          | ~ l1_struct_0(X0)
          | v2_struct_0(X0) )
    | ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) )).

tff(u108,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u107,axiom,
    ( ~ ! [X0] :
          ( ~ l1_orders_2(X0)
          | l1_struct_0(X0) )
    | ! [X0] :
        ( ~ l1_orders_2(X0)
        | l1_struct_0(X0) ) )).

tff(u106,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u105,axiom,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,X0)
          | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
          | v1_xboole_0(X0) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
        | v1_xboole_0(X0) ) )).

tff(u104,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (22245)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (22244)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (22242)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (22253)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (22241)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (22243)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (22245)# SZS output start Saturation.
% 0.20/0.50  tff(u113,negated_conjecture,
% 0.20/0.50      ((~(sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) | (sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u112,negated_conjecture,
% 0.20/0.50      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))).
% 0.20/0.50  
% 0.20/0.50  tff(u111,negated_conjecture,
% 0.20/0.50      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u110,negated_conjecture,
% 0.20/0.50      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u109,axiom,
% 0.20/0.50      ((~(![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))) | (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u108,negated_conjecture,
% 0.20/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u107,axiom,
% 0.20/0.50      ((~(![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))) | (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u106,negated_conjecture,
% 0.20/0.50      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u105,axiom,
% 0.20/0.50      ((~(![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | v1_xboole_0(X0))))) | (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | v1_xboole_0(X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u104,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  % (22245)# SZS output end Saturation.
% 0.20/0.50  % (22245)------------------------------
% 0.20/0.50  % (22245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (22245)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (22245)Memory used [KB]: 6140
% 0.20/0.50  % (22245)Time elapsed: 0.065 s
% 0.20/0.50  % (22245)------------------------------
% 0.20/0.50  % (22245)------------------------------
% 0.20/0.50  % (22252)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (22237)Success in time 0.14 s
%------------------------------------------------------------------------------
