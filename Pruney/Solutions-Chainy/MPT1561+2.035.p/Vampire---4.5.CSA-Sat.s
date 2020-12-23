%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:12 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   45 (  45 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u113,negated_conjecture,
    ( ~ ( sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)) )
    | sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u112,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k2_tarski(sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

tff(u111,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u110,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u109,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u108,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u107,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u106,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) )).

tff(u105,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_orders_2(X0,X1,X1) ) )).

tff(u104,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u103,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u102,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | X1 = X2 ) )).

tff(u101,negated_conjecture,
    ( ~ ( sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)) )
    | ! [X0] :
        ( ~ r1_orders_2(X0,k2_yellow_0(sK0,k2_tarski(sK1,sK1)),sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(sK1,u1_struct_0(X0))
        | ~ m1_subset_1(k2_yellow_0(sK0,k2_tarski(sK1,sK1)),u1_struct_0(X0))
        | ~ v5_orders_2(X0)
        | ~ r1_orders_2(X0,sK1,k2_yellow_0(sK0,k2_tarski(sK1,sK1))) ) )).

tff(u100,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | r1_orders_2(sK0,sK1,sK1) )).

tff(u99,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (24547)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (24566)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (24548)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (24558)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (24550)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (24548)Refutation not found, incomplete strategy% (24548)------------------------------
% 0.21/0.53  % (24548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24556)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (24550)Refutation not found, incomplete strategy% (24550)------------------------------
% 0.21/0.53  % (24550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24550)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24550)Memory used [KB]: 10618
% 0.21/0.53  % (24550)Time elapsed: 0.103 s
% 0.21/0.53  % (24550)------------------------------
% 0.21/0.53  % (24550)------------------------------
% 0.21/0.53  % (24547)Refutation not found, incomplete strategy% (24547)------------------------------
% 0.21/0.53  % (24547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24547)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24547)Memory used [KB]: 10618
% 0.21/0.53  % (24547)Time elapsed: 0.104 s
% 0.21/0.53  % (24547)------------------------------
% 0.21/0.53  % (24547)------------------------------
% 0.21/0.53  % (24556)Refutation not found, incomplete strategy% (24556)------------------------------
% 0.21/0.53  % (24556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24556)Memory used [KB]: 10618
% 0.21/0.53  % (24556)Time elapsed: 0.117 s
% 0.21/0.53  % (24556)------------------------------
% 0.21/0.53  % (24556)------------------------------
% 0.21/0.54  % (24564)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (24563)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (24555)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (24558)Refutation not found, incomplete strategy% (24558)------------------------------
% 0.21/0.54  % (24558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24558)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24558)Memory used [KB]: 10746
% 0.21/0.54  % (24558)Time elapsed: 0.117 s
% 0.21/0.54  % (24558)------------------------------
% 0.21/0.54  % (24558)------------------------------
% 0.21/0.54  % (24564)Refutation not found, incomplete strategy% (24564)------------------------------
% 0.21/0.54  % (24564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24564)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24564)Memory used [KB]: 6268
% 0.21/0.54  % (24564)Time elapsed: 0.118 s
% 0.21/0.54  % (24564)------------------------------
% 0.21/0.54  % (24564)------------------------------
% 0.21/0.54  % (24548)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24548)Memory used [KB]: 10746
% 0.21/0.54  % (24548)Time elapsed: 0.105 s
% 0.21/0.54  % (24548)------------------------------
% 0.21/0.54  % (24548)------------------------------
% 0.21/0.54  % (24566)Refutation not found, incomplete strategy% (24566)------------------------------
% 0.21/0.54  % (24566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24566)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24566)Memory used [KB]: 6268
% 0.21/0.54  % (24566)Time elapsed: 0.116 s
% 0.21/0.54  % (24566)------------------------------
% 0.21/0.54  % (24566)------------------------------
% 0.21/0.54  % (24563)Refutation not found, incomplete strategy% (24563)------------------------------
% 0.21/0.54  % (24563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24563)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24563)Memory used [KB]: 6268
% 0.21/0.54  % (24563)Time elapsed: 0.122 s
% 0.21/0.54  % (24563)------------------------------
% 0.21/0.54  % (24563)------------------------------
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (24555)# SZS output start Saturation.
% 0.21/0.54  tff(u113,negated_conjecture,
% 0.21/0.54      ((~(sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)))) | (sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u112,negated_conjecture,
% 0.21/0.54      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u111,negated_conjecture,
% 0.21/0.54      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u110,negated_conjecture,
% 0.21/0.54      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u109,axiom,
% 0.21/0.54      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u108,axiom,
% 0.21/0.54      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u107,negated_conjecture,
% 0.21/0.54      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u106,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u105,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u104,negated_conjecture,
% 0.21/0.54      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u103,negated_conjecture,
% 0.21/0.54      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u102,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | (X1 = X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u101,negated_conjecture,
% 0.21/0.54      ((~(sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)))) | (![X0] : ((~r1_orders_2(X0,k2_yellow_0(sK0,k2_tarski(sK1,sK1)),sK1) | ~l1_orders_2(X0) | ~m1_subset_1(sK1,u1_struct_0(X0)) | ~m1_subset_1(k2_yellow_0(sK0,k2_tarski(sK1,sK1)),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,sK1,k2_yellow_0(sK0,k2_tarski(sK1,sK1)))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u100,negated_conjecture,
% 0.21/0.54      ((~r1_orders_2(sK0,sK1,sK1)) | r1_orders_2(sK0,sK1,sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u99,negated_conjecture,
% 0.21/0.54      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.21/0.54  
% 0.21/0.54  % (24555)# SZS output end Saturation.
% 0.21/0.54  % (24555)------------------------------
% 0.21/0.54  % (24555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24555)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (24555)Memory used [KB]: 10746
% 0.21/0.54  % (24555)Time elapsed: 0.123 s
% 0.21/0.54  % (24555)------------------------------
% 0.21/0.54  % (24555)------------------------------
% 0.21/0.54  % (24538)Success in time 0.176 s
%------------------------------------------------------------------------------
