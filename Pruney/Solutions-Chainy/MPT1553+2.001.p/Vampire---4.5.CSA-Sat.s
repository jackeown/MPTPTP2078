%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:03 EST 2020

% Result     : CounterSatisfiable 0.23s
% Output     : Saturation 0.23s
% Verified   : 
% Statistics : Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   47 (  47 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | r2_yellow_0(sK0,sK2) )).

cnf(u31,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | sK1 = k2_yellow_0(sK0,sK2) )).

cnf(u22,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | r2_yellow_0(sK0,sK2)
    | sK1 = k2_yellow_0(sK0,sK2) )).

cnf(u10,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | sK1 != k2_yellow_0(sK0,sK2)
    | ~ r2_yellow_0(sK0,sK2) )).

cnf(u13,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,X3)
    | r1_orders_2(sK0,X3,sK1) )).

cnf(u16,negated_conjecture,
    ( r1_lattice3(sK0,sK2,sK1)
    | r2_yellow_0(sK0,sK2) )).

cnf(u17,negated_conjecture,
    ( r1_lattice3(sK0,sK2,sK1)
    | sK1 = k2_yellow_0(sK0,sK2) )).

cnf(u8,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | sK1 != k2_yellow_0(sK0,sK2)
    | ~ r2_yellow_0(sK0,sK2) )).

cnf(u9,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | r1_lattice3(sK0,sK2,sK3)
    | sK1 != k2_yellow_0(sK0,sK2)
    | ~ r2_yellow_0(sK0,sK2) )).

cnf(u11,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,X3)
    | r1_orders_2(sK0,X3,sK1) )).

cnf(u12,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,X3)
    | r1_orders_2(sK0,X3,sK1) )).

cnf(u15,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK2)
    | r1_orders_2(sK0,X3,sK1) )).

cnf(u14,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | sK1 = k2_yellow_0(sK0,sK2)
    | r1_orders_2(sK0,X3,sK1) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:27:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.48  % (30173)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.49  % (30173)Refutation not found, incomplete strategy% (30173)------------------------------
% 0.23/0.49  % (30173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (30173)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (30173)Memory used [KB]: 6140
% 0.23/0.49  % (30173)Time elapsed: 0.067 s
% 0.23/0.49  % (30173)------------------------------
% 0.23/0.49  % (30173)------------------------------
% 0.23/0.50  % (30181)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.50  % (30181)Refutation not found, incomplete strategy% (30181)------------------------------
% 0.23/0.50  % (30181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (30181)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (30181)Memory used [KB]: 1663
% 0.23/0.50  % (30181)Time elapsed: 0.068 s
% 0.23/0.50  % (30181)------------------------------
% 0.23/0.50  % (30181)------------------------------
% 0.23/0.52  % (30169)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.52  % (30171)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.52  % (30169)Refutation not found, incomplete strategy% (30169)------------------------------
% 0.23/0.52  % (30169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (30169)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (30169)Memory used [KB]: 10618
% 0.23/0.52  % (30169)Time elapsed: 0.090 s
% 0.23/0.52  % (30169)------------------------------
% 0.23/0.52  % (30169)------------------------------
% 0.23/0.52  % (30171)Refutation not found, incomplete strategy% (30171)------------------------------
% 0.23/0.52  % (30171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (30171)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (30171)Memory used [KB]: 10618
% 0.23/0.52  % (30171)Time elapsed: 0.083 s
% 0.23/0.52  % (30171)------------------------------
% 0.23/0.52  % (30171)------------------------------
% 0.23/0.52  % (30174)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.52  % (30174)Refutation not found, incomplete strategy% (30174)------------------------------
% 0.23/0.52  % (30174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (30174)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (30174)Memory used [KB]: 10618
% 0.23/0.52  % (30174)Time elapsed: 0.091 s
% 0.23/0.52  % (30174)------------------------------
% 0.23/0.52  % (30174)------------------------------
% 0.23/0.52  % (30178)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.23/0.52  % (30178)Refutation not found, incomplete strategy% (30178)------------------------------
% 0.23/0.52  % (30178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (30178)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (30178)Memory used [KB]: 6140
% 0.23/0.52  % (30178)Time elapsed: 0.087 s
% 0.23/0.52  % (30178)------------------------------
% 0.23/0.52  % (30178)------------------------------
% 0.23/0.53  % (30184)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.23/0.53  % (30170)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.23/0.53  % (30170)Refutation not found, incomplete strategy% (30170)------------------------------
% 0.23/0.53  % (30170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (30170)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (30170)Memory used [KB]: 10618
% 0.23/0.53  % (30170)Time elapsed: 0.085 s
% 0.23/0.53  % (30170)------------------------------
% 0.23/0.53  % (30170)------------------------------
% 0.23/0.53  % (30184)Refutation not found, incomplete strategy% (30184)------------------------------
% 0.23/0.53  % (30184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (30184)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (30184)Memory used [KB]: 10618
% 0.23/0.53  % (30184)Time elapsed: 0.090 s
% 0.23/0.53  % (30184)------------------------------
% 0.23/0.53  % (30184)------------------------------
% 0.23/0.53  % (30183)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.53  % (30179)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.23/0.53  % (30183)Refutation not found, incomplete strategy% (30183)------------------------------
% 0.23/0.53  % (30183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (30183)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (30183)Memory used [KB]: 6140
% 0.23/0.53  % (30183)Time elapsed: 0.058 s
% 0.23/0.53  % (30183)------------------------------
% 0.23/0.53  % (30183)------------------------------
% 0.23/0.53  % (30182)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.53  % (30168)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.53  % (30179)Refutation not found, incomplete strategy% (30179)------------------------------
% 0.23/0.53  % (30179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (30179)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (30179)Memory used [KB]: 10618
% 0.23/0.53  % (30179)Time elapsed: 0.095 s
% 0.23/0.53  % (30179)------------------------------
% 0.23/0.53  % (30179)------------------------------
% 0.23/0.53  % (30168)Refutation not found, incomplete strategy% (30168)------------------------------
% 0.23/0.53  % (30168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (30168)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (30168)Memory used [KB]: 6140
% 0.23/0.53  % (30168)Time elapsed: 0.101 s
% 0.23/0.53  % (30168)------------------------------
% 0.23/0.53  % (30168)------------------------------
% 0.23/0.54  % (30175)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.23/0.54  % (30188)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.23/0.54  % (30177)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.23/0.54  % (30188)Refutation not found, incomplete strategy% (30188)------------------------------
% 0.23/0.54  % (30188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (30188)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (30188)Memory used [KB]: 10618
% 0.23/0.54  % (30188)Time elapsed: 0.108 s
% 0.23/0.54  % (30188)------------------------------
% 0.23/0.54  % (30188)------------------------------
% 0.23/0.54  % (30172)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.54  % (30176)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.54  % (30172)Refutation not found, incomplete strategy% (30172)------------------------------
% 0.23/0.54  % (30172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (30172)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (30172)Memory used [KB]: 1535
% 0.23/0.54  % (30172)Time elapsed: 0.108 s
% 0.23/0.54  % (30172)------------------------------
% 0.23/0.54  % (30172)------------------------------
% 0.23/0.54  % (30177)Refutation not found, incomplete strategy% (30177)------------------------------
% 0.23/0.54  % (30177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (30177)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (30177)Memory used [KB]: 10618
% 0.23/0.54  % (30177)Time elapsed: 0.110 s
% 0.23/0.54  % (30177)------------------------------
% 0.23/0.54  % (30177)------------------------------
% 0.23/0.55  % (30186)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.23/0.55  % (30186)Refutation not found, incomplete strategy% (30186)------------------------------
% 0.23/0.55  % (30186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (30186)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (30186)Memory used [KB]: 1663
% 0.23/0.55  % (30186)Time elapsed: 0.110 s
% 0.23/0.55  % (30186)------------------------------
% 0.23/0.55  % (30186)------------------------------
% 0.23/0.55  % (30185)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.23/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.23/0.55  % (30185)# SZS output start Saturation.
% 0.23/0.55  cnf(u23,negated_conjecture,
% 0.23/0.55      r1_orders_2(sK0,sK1,sK1) | r2_yellow_0(sK0,sK2)).
% 0.23/0.55  
% 0.23/0.55  cnf(u31,negated_conjecture,
% 0.23/0.55      r1_orders_2(sK0,sK1,sK1) | sK1 = k2_yellow_0(sK0,sK2)).
% 0.23/0.55  
% 0.23/0.55  cnf(u22,negated_conjecture,
% 0.23/0.55      r1_orders_2(sK0,sK1,sK1) | r2_yellow_0(sK0,sK2) | sK1 = k2_yellow_0(sK0,sK2)).
% 0.23/0.55  
% 0.23/0.55  cnf(u10,negated_conjecture,
% 0.23/0.55      ~r1_orders_2(sK0,sK3,sK1) | ~r1_lattice3(sK0,sK2,sK1) | sK1 != k2_yellow_0(sK0,sK2) | ~r2_yellow_0(sK0,sK2)).
% 0.23/0.55  
% 0.23/0.55  cnf(u13,negated_conjecture,
% 0.23/0.55      ~r1_orders_2(sK0,sK3,sK1) | ~r1_lattice3(sK0,sK2,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK2,X3) | r1_orders_2(sK0,X3,sK1)).
% 0.23/0.55  
% 0.23/0.55  cnf(u16,negated_conjecture,
% 0.23/0.55      r1_lattice3(sK0,sK2,sK1) | r2_yellow_0(sK0,sK2)).
% 0.23/0.55  
% 0.23/0.55  cnf(u17,negated_conjecture,
% 0.23/0.55      r1_lattice3(sK0,sK2,sK1) | sK1 = k2_yellow_0(sK0,sK2)).
% 0.23/0.55  
% 0.23/0.55  cnf(u8,negated_conjecture,
% 0.23/0.55      ~r1_lattice3(sK0,sK2,sK1) | m1_subset_1(sK3,u1_struct_0(sK0)) | sK1 != k2_yellow_0(sK0,sK2) | ~r2_yellow_0(sK0,sK2)).
% 0.23/0.55  
% 0.23/0.55  cnf(u9,negated_conjecture,
% 0.23/0.55      ~r1_lattice3(sK0,sK2,sK1) | r1_lattice3(sK0,sK2,sK3) | sK1 != k2_yellow_0(sK0,sK2) | ~r2_yellow_0(sK0,sK2)).
% 0.23/0.55  
% 0.23/0.55  cnf(u11,negated_conjecture,
% 0.23/0.55      ~r1_lattice3(sK0,sK2,sK1) | m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK2,X3) | r1_orders_2(sK0,X3,sK1)).
% 0.23/0.55  
% 0.23/0.55  cnf(u12,negated_conjecture,
% 0.23/0.55      ~r1_lattice3(sK0,sK2,sK1) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK2,X3) | r1_orders_2(sK0,X3,sK1)).
% 0.23/0.55  
% 0.23/0.55  cnf(u15,negated_conjecture,
% 0.23/0.55      ~r1_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_yellow_0(sK0,sK2) | r1_orders_2(sK0,X3,sK1)).
% 0.23/0.55  
% 0.23/0.55  cnf(u14,negated_conjecture,
% 0.23/0.55      ~r1_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK1 = k2_yellow_0(sK0,sK2) | r1_orders_2(sK0,X3,sK1)).
% 0.23/0.55  
% 0.23/0.55  cnf(u18,negated_conjecture,
% 0.23/0.55      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.23/0.55  
% 0.23/0.55  % (30185)# SZS output end Saturation.
% 0.23/0.55  % (30185)------------------------------
% 0.23/0.55  % (30185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (30185)Termination reason: Satisfiable
% 0.23/0.55  
% 0.23/0.55  % (30185)Memory used [KB]: 1663
% 0.23/0.55  % (30185)Time elapsed: 0.092 s
% 0.23/0.55  % (30185)------------------------------
% 0.23/0.55  % (30185)------------------------------
% 0.23/0.55  % (30167)Success in time 0.183 s
%------------------------------------------------------------------------------
