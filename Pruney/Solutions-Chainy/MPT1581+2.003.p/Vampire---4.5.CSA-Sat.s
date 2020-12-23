%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:22 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u105,negated_conjecture,
    ( sK3 != sK5
    | sK3 = sK5 )).

tff(u104,negated_conjecture,
    ( sK2 != sK4
    | sK2 = sK4 )).

tff(u103,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) )).

tff(u102,negated_conjecture,
    ( ~ ~ l1_orders_2(sK1)
    | ~ l1_orders_2(sK1) )).

tff(u101,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u100,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u99,negated_conjecture,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | m1_subset_1(sK3,u1_struct_0(sK0)) )).

tff(u98,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u97,negated_conjecture,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u96,negated_conjecture,
    ( ~ ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3) )).

tff(u95,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u94,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | r1_orders_2(sK1,sK2,sK3) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (27827)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.46  % (27811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.46  % (27811)Refutation not found, incomplete strategy% (27811)------------------------------
% 0.20/0.46  % (27811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (27811)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (27811)Memory used [KB]: 6140
% 0.20/0.46  % (27811)Time elapsed: 0.047 s
% 0.20/0.46  % (27811)------------------------------
% 0.20/0.46  % (27811)------------------------------
% 0.20/0.51  % (27808)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (27808)Refutation not found, incomplete strategy% (27808)------------------------------
% 0.20/0.51  % (27808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27808)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27808)Memory used [KB]: 6140
% 0.20/0.51  % (27808)Time elapsed: 0.099 s
% 0.20/0.51  % (27808)------------------------------
% 0.20/0.51  % (27808)------------------------------
% 0.20/0.51  % (27804)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (27804)Refutation not found, incomplete strategy% (27804)------------------------------
% 0.20/0.51  % (27804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27804)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27804)Memory used [KB]: 1663
% 0.20/0.51  % (27804)Time elapsed: 0.094 s
% 0.20/0.51  % (27804)------------------------------
% 0.20/0.51  % (27804)------------------------------
% 0.20/0.51  % (27812)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (27812)Refutation not found, incomplete strategy% (27812)------------------------------
% 0.20/0.52  % (27812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27812)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27812)Memory used [KB]: 10618
% 0.20/0.52  % (27812)Time elapsed: 0.099 s
% 0.20/0.52  % (27812)------------------------------
% 0.20/0.52  % (27812)------------------------------
% 0.20/0.53  % (27816)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (27807)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (27832)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (27824)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (27805)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (27809)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (27809)Refutation not found, incomplete strategy% (27809)------------------------------
% 0.20/0.54  % (27809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27809)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27809)Memory used [KB]: 6140
% 0.20/0.54  % (27809)Time elapsed: 0.126 s
% 0.20/0.54  % (27809)------------------------------
% 0.20/0.54  % (27809)------------------------------
% 0.20/0.54  % (27817)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (27824)Refutation not found, incomplete strategy% (27824)------------------------------
% 0.20/0.54  % (27824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27824)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27824)Memory used [KB]: 10746
% 0.20/0.54  % (27824)Time elapsed: 0.131 s
% 0.20/0.54  % (27824)------------------------------
% 0.20/0.54  % (27824)------------------------------
% 0.20/0.54  % (27829)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (27829)Refutation not found, incomplete strategy% (27829)------------------------------
% 0.20/0.54  % (27829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27829)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27829)Memory used [KB]: 6268
% 0.20/0.54  % (27829)Time elapsed: 0.129 s
% 0.20/0.54  % (27829)------------------------------
% 0.20/0.54  % (27829)------------------------------
% 0.20/0.54  % (27823)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (27821)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (27823)Refutation not found, incomplete strategy% (27823)------------------------------
% 0.20/0.54  % (27823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27823)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27823)Memory used [KB]: 10746
% 0.20/0.54  % (27823)Time elapsed: 0.137 s
% 0.20/0.54  % (27823)------------------------------
% 0.20/0.54  % (27823)------------------------------
% 0.20/0.54  % (27821)Refutation not found, incomplete strategy% (27821)------------------------------
% 0.20/0.54  % (27821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27821)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27821)Memory used [KB]: 10618
% 0.20/0.54  % (27821)Time elapsed: 0.138 s
% 0.20/0.54  % (27821)------------------------------
% 0.20/0.54  % (27821)------------------------------
% 0.20/0.55  % (27833)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (27825)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (27810)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (27833)Refutation not found, incomplete strategy% (27833)------------------------------
% 0.20/0.55  % (27833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27831)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (27826)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (27833)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (27833)Memory used [KB]: 1663
% 0.20/0.55  % (27833)Time elapsed: 0.141 s
% 0.20/0.55  % (27833)------------------------------
% 0.20/0.55  % (27833)------------------------------
% 0.20/0.55  % (27825)Refutation not found, incomplete strategy% (27825)------------------------------
% 0.20/0.55  % (27825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27825)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  % (27826)Refutation not found, incomplete strategy% (27826)------------------------------
% 0.20/0.55  % (27826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27826)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (27826)Memory used [KB]: 10746
% 0.20/0.55  % (27826)Time elapsed: 0.124 s
% 0.20/0.55  % (27826)------------------------------
% 0.20/0.55  % (27826)------------------------------
% 0.20/0.55  
% 0.20/0.55  % (27825)Memory used [KB]: 1663
% 0.20/0.55  % (27825)Time elapsed: 0.150 s
% 0.20/0.55  % (27825)------------------------------
% 0.20/0.55  % (27825)------------------------------
% 0.20/0.55  % (27813)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (27813)Refutation not found, incomplete strategy% (27813)------------------------------
% 0.20/0.55  % (27813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27813)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (27813)Memory used [KB]: 10618
% 0.20/0.55  % (27813)Time elapsed: 0.149 s
% 0.20/0.55  % (27813)------------------------------
% 0.20/0.55  % (27813)------------------------------
% 0.20/0.55  % (27818)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (27815)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (27815)Refutation not found, incomplete strategy% (27815)------------------------------
% 0.20/0.55  % (27815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27815)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (27815)Memory used [KB]: 10618
% 0.20/0.55  % (27815)Time elapsed: 0.149 s
% 0.20/0.55  % (27815)------------------------------
% 0.20/0.55  % (27815)------------------------------
% 0.20/0.56  % (27828)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (27814)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (27806)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.56  % (27806)Refutation not found, incomplete strategy% (27806)------------------------------
% 0.20/0.56  % (27806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (27806)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (27806)Memory used [KB]: 10618
% 0.20/0.56  % (27806)Time elapsed: 0.156 s
% 0.20/0.56  % (27806)------------------------------
% 0.20/0.56  % (27806)------------------------------
% 0.20/0.57  % (27830)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.57  % (27819)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.57  % (27822)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (27820)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.57  % (27830)Refutation not found, incomplete strategy% (27830)------------------------------
% 0.20/0.57  % (27830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.57  % (27814)Refutation not found, incomplete strategy% (27814)------------------------------
% 0.20/0.57  % (27814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (27814)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (27814)Memory used [KB]: 10618
% 0.20/0.58  % (27814)Time elapsed: 0.173 s
% 0.20/0.58  % (27814)------------------------------
% 0.20/0.58  % (27814)------------------------------
% 0.20/0.58  % (27834)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.20/0.58  % (27830)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (27830)Memory used [KB]: 10618
% 0.20/0.58  % (27830)Time elapsed: 0.172 s
% 0.20/0.58  % (27830)------------------------------
% 0.20/0.58  % (27830)------------------------------
% 0.20/0.58  % (27834)Refutation not found, incomplete strategy% (27834)------------------------------
% 0.20/0.58  % (27834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (27834)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (27834)Memory used [KB]: 6140
% 0.20/0.58  % (27834)Time elapsed: 0.045 s
% 0.20/0.58  % (27834)------------------------------
% 0.20/0.58  % (27834)------------------------------
% 0.20/0.58  % (27820)# SZS output start Saturation.
% 0.20/0.58  tff(u105,negated_conjecture,
% 0.20/0.58      ((~(sK3 = sK5)) | (sK3 = sK5))).
% 0.20/0.58  
% 0.20/0.58  tff(u104,negated_conjecture,
% 0.20/0.58      ((~(sK2 = sK4)) | (sK2 = sK4))).
% 0.20/0.58  
% 0.20/0.58  tff(u103,axiom,
% 0.20/0.58      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2))))).
% 0.20/0.58  
% 0.20/0.58  tff(u102,negated_conjecture,
% 0.20/0.58      ((~~l1_orders_2(sK1)) | ~l1_orders_2(sK1))).
% 0.20/0.58  
% 0.20/0.58  tff(u101,negated_conjecture,
% 0.20/0.58      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.58  
% 0.20/0.58  tff(u100,negated_conjecture,
% 0.20/0.58      ((~m1_subset_1(sK2,u1_struct_0(sK0))) | m1_subset_1(sK2,u1_struct_0(sK0)))).
% 0.20/0.58  
% 0.20/0.58  tff(u99,negated_conjecture,
% 0.20/0.58      ((~m1_subset_1(sK3,u1_struct_0(sK0))) | m1_subset_1(sK3,u1_struct_0(sK0)))).
% 0.20/0.58  
% 0.20/0.58  tff(u98,negated_conjecture,
% 0.20/0.58      ((~m1_subset_1(sK2,u1_struct_0(sK1))) | m1_subset_1(sK2,u1_struct_0(sK1)))).
% 0.20/0.58  
% 0.20/0.58  tff(u97,negated_conjecture,
% 0.20/0.58      ((~m1_subset_1(sK3,u1_struct_0(sK1))) | m1_subset_1(sK3,u1_struct_0(sK1)))).
% 0.20/0.58  
% 0.20/0.58  tff(u96,negated_conjecture,
% 0.20/0.58      ((~~r1_orders_2(sK0,sK2,sK3)) | ~r1_orders_2(sK0,sK2,sK3))).
% 0.20/0.58  
% 0.20/0.58  tff(u95,axiom,
% 0.20/0.58      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.58  
% 0.20/0.58  tff(u94,negated_conjecture,
% 0.20/0.58      ((~r1_orders_2(sK1,sK2,sK3)) | r1_orders_2(sK1,sK2,sK3))).
% 0.20/0.58  
% 0.20/0.58  % (27820)# SZS output end Saturation.
% 0.20/0.58  % (27820)------------------------------
% 0.20/0.58  % (27820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (27820)Termination reason: Satisfiable
% 0.20/0.58  
% 0.20/0.58  % (27820)Memory used [KB]: 10746
% 0.20/0.58  % (27820)Time elapsed: 0.172 s
% 0.20/0.58  % (27820)------------------------------
% 0.20/0.58  % (27820)------------------------------
% 0.20/0.58  % (27803)Success in time 0.214 s
%------------------------------------------------------------------------------
