%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:13 EST 2020

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (22898)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (22913)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (22889)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (22889)Refutation not found, incomplete strategy% (22889)------------------------------
% 0.21/0.51  % (22889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22889)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22889)Memory used [KB]: 6268
% 0.21/0.51  % (22889)Time elapsed: 0.106 s
% 0.21/0.51  % (22889)------------------------------
% 0.21/0.51  % (22889)------------------------------
% 0.21/0.51  % (22885)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (22892)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (22892)Refutation not found, incomplete strategy% (22892)------------------------------
% 0.21/0.52  % (22892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22892)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22892)Memory used [KB]: 6140
% 0.21/0.52  % (22892)Time elapsed: 0.115 s
% 0.21/0.52  % (22892)------------------------------
% 0.21/0.52  % (22892)------------------------------
% 0.21/0.52  % (22885)Refutation not found, incomplete strategy% (22885)------------------------------
% 0.21/0.52  % (22885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22885)Memory used [KB]: 1663
% 0.21/0.52  % (22885)Time elapsed: 0.112 s
% 0.21/0.52  % (22885)------------------------------
% 0.21/0.52  % (22885)------------------------------
% 0.21/0.52  % (22904)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (22905)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (22905)Refutation not found, incomplete strategy% (22905)------------------------------
% 0.21/0.52  % (22905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22905)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22905)Memory used [KB]: 10746
% 0.21/0.52  % (22905)Time elapsed: 0.115 s
% 0.21/0.52  % (22905)------------------------------
% 0.21/0.52  % (22905)------------------------------
% 0.21/0.53  % (22887)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (22896)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (22887)Refutation not found, incomplete strategy% (22887)------------------------------
% 0.21/0.53  % (22887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22887)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22887)Memory used [KB]: 10618
% 0.21/0.53  % (22887)Time elapsed: 0.122 s
% 0.21/0.53  % (22887)------------------------------
% 0.21/0.53  % (22887)------------------------------
% 0.21/0.53  % (22912)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (22912)Refutation not found, incomplete strategy% (22912)------------------------------
% 0.21/0.53  % (22912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22912)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22912)Memory used [KB]: 6268
% 0.21/0.53  % (22912)Time elapsed: 0.130 s
% 0.21/0.53  % (22912)------------------------------
% 0.21/0.53  % (22912)------------------------------
% 0.21/0.53  % (22890)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (22904)Refutation not found, incomplete strategy% (22904)------------------------------
% 0.21/0.53  % (22904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22904)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22904)Memory used [KB]: 10746
% 0.21/0.53  % (22904)Time elapsed: 0.131 s
% 0.21/0.53  % (22904)------------------------------
% 0.21/0.53  % (22904)------------------------------
% 0.21/0.53  % (22888)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (22890)Refutation not found, incomplete strategy% (22890)------------------------------
% 0.21/0.53  % (22890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22890)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22890)Memory used [KB]: 6268
% 0.21/0.53  % (22890)Time elapsed: 0.134 s
% 0.21/0.53  % (22890)------------------------------
% 0.21/0.53  % (22890)------------------------------
% 0.21/0.54  % (22901)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (22896)Refutation not found, incomplete strategy% (22896)------------------------------
% 0.21/0.54  % (22896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22896)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22896)Memory used [KB]: 10618
% 0.21/0.54  % (22896)Time elapsed: 0.141 s
% 0.21/0.54  % (22896)------------------------------
% 0.21/0.54  % (22896)------------------------------
% 0.21/0.54  % (22907)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (22888)Refutation not found, incomplete strategy% (22888)------------------------------
% 0.21/0.54  % (22888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22888)Memory used [KB]: 10618
% 0.21/0.54  % (22888)Time elapsed: 0.134 s
% 0.21/0.54  % (22888)------------------------------
% 0.21/0.54  % (22888)------------------------------
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (22901)# SZS output start Saturation.
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
% 0.21/0.54  % (22901)# SZS output end Saturation.
% 0.21/0.54  % (22901)------------------------------
% 0.21/0.54  % (22901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22901)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (22901)Memory used [KB]: 10746
% 0.21/0.54  % (22901)Time elapsed: 0.135 s
% 0.21/0.54  % (22901)------------------------------
% 0.21/0.54  % (22901)------------------------------
% 0.21/0.54  % (22886)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (22893)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (22910)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (22906)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (22893)Refutation not found, incomplete strategy% (22893)------------------------------
% 0.21/0.54  % (22893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22893)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22893)Memory used [KB]: 10618
% 0.21/0.54  % (22893)Time elapsed: 0.135 s
% 0.21/0.54  % (22893)------------------------------
% 0.21/0.54  % (22893)------------------------------
% 0.21/0.54  % (22906)Refutation not found, incomplete strategy% (22906)------------------------------
% 0.21/0.54  % (22906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22906)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22906)Memory used [KB]: 1663
% 0.21/0.54  % (22906)Time elapsed: 0.139 s
% 0.21/0.54  % (22906)------------------------------
% 0.21/0.54  % (22906)------------------------------
% 0.21/0.54  % (22895)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (22894)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (22897)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (22900)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (22903)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (22902)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (22897)Refutation not found, incomplete strategy% (22897)------------------------------
% 0.21/0.55  % (22897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22897)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22897)Memory used [KB]: 6140
% 0.21/0.55  % (22897)Time elapsed: 0.148 s
% 0.21/0.55  % (22897)------------------------------
% 0.21/0.55  % (22897)------------------------------
% 0.21/0.55  % (22900)Refutation not found, incomplete strategy% (22900)------------------------------
% 0.21/0.55  % (22900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22902)Refutation not found, incomplete strategy% (22902)------------------------------
% 0.21/0.55  % (22902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22902)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22902)Memory used [KB]: 10618
% 0.21/0.55  % (22902)Time elapsed: 0.146 s
% 0.21/0.55  % (22902)------------------------------
% 0.21/0.55  % (22902)------------------------------
% 0.21/0.55  % (22909)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (22914)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (22884)Success in time 0.183 s
%------------------------------------------------------------------------------
