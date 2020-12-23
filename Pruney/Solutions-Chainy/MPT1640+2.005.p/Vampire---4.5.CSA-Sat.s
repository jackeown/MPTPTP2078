%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:00 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :   50 (  50 expanded)
%              Number of leaves         :   50 (  50 expanded)
%              Depth                    :    0
%              Number of atoms          :  198 ( 198 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal clause size      :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u197,negated_conjecture,
    ( r1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

cnf(u172,negated_conjecture,
    ( r1_yellow_0(sK0,k2_tarski(sK2,sK2)) )).

cnf(u21,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u136,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK3(sK0,sK1,sK1,sK1))
    | r1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

cnf(u63,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u131,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3(sK0,sK2,sK2,sK2))
    | r1_yellow_0(sK0,k2_tarski(sK2,sK2)) )).

cnf(u55,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2) )).

cnf(u112,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,X0,sK1),u1_struct_0(sK0))
    | r1_yellow_0(sK0,k2_tarski(sK1,X0)) )).

cnf(u115,negated_conjecture,
    ( ~ r1_orders_2(sK0,X1,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X1,sK1))
    | r1_yellow_0(sK0,k2_tarski(sK1,X1)) )).

cnf(u118,negated_conjecture,
    ( ~ r1_orders_2(sK0,X2,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | r1_orders_2(sK0,X2,sK3(sK0,sK1,X2,sK1))
    | r1_yellow_0(sK0,k2_tarski(sK1,X2)) )).

cnf(u121,negated_conjecture,
    ( ~ r1_orders_2(sK0,X3,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,X3,sK1),u1_struct_0(sK0))
    | sK1 = k10_lattice3(sK0,sK1,X3) )).

cnf(u124,negated_conjecture,
    ( ~ r1_orders_2(sK0,X4,sK1)
    | ~ m1_subset_1(X4,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X4,sK1))
    | sK1 = k10_lattice3(sK0,sK1,X4) )).

cnf(u127,negated_conjecture,
    ( ~ r1_orders_2(sK0,X5,sK1)
    | ~ m1_subset_1(X5,u1_struct_0(sK0))
    | r1_orders_2(sK0,X5,sK3(sK0,sK1,X5,sK1))
    | sK1 = k10_lattice3(sK0,sK1,X5) )).

cnf(u80,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK2,X0,sK2),u1_struct_0(sK0))
    | r1_yellow_0(sK0,k2_tarski(sK2,X0)) )).

cnf(u83,negated_conjecture,
    ( ~ r1_orders_2(sK0,X1,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK3(sK0,sK2,X1,sK2))
    | r1_yellow_0(sK0,k2_tarski(sK2,X1)) )).

cnf(u86,negated_conjecture,
    ( ~ r1_orders_2(sK0,X2,sK2)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | r1_orders_2(sK0,X2,sK3(sK0,sK2,X2,sK2))
    | r1_yellow_0(sK0,k2_tarski(sK2,X2)) )).

cnf(u89,negated_conjecture,
    ( ~ r1_orders_2(sK0,X3,sK2)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK2,X3,sK2),u1_struct_0(sK0))
    | sK2 = k10_lattice3(sK0,sK2,X3) )).

cnf(u92,negated_conjecture,
    ( ~ r1_orders_2(sK0,X4,sK2)
    | ~ m1_subset_1(X4,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK3(sK0,sK2,X4,sK2))
    | sK2 = k10_lattice3(sK0,sK2,X4) )).

cnf(u95,negated_conjecture,
    ( ~ r1_orders_2(sK0,X5,sK2)
    | ~ m1_subset_1(X5,u1_struct_0(sK0))
    | r1_orders_2(sK0,X5,sK3(sK0,sK2,X5,sK2))
    | sK2 = k10_lattice3(sK0,sK2,X5) )).

cnf(u27,axiom,
    ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ v5_orders_2(X0)
    | r1_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u31,axiom,
    ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ v5_orders_2(X0)
    | k10_lattice3(X0,X1,X2) = X3 )).

cnf(u35,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | r3_orders_2(X0,X1,X2) )).

cnf(u30,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
    | k10_lattice3(X0,X1,X2) = X3 )).

cnf(u29,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
    | k10_lattice3(X0,X1,X2) = X3 )).

cnf(u28,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
    | k10_lattice3(X0,X1,X2) = X3 )).

cnf(u26,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
    | r1_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u25,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
    | r1_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u24,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
    | r1_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u56,negated_conjecture,
    ( r3_orders_2(sK0,sK1,sK1) )).

cnf(u48,negated_conjecture,
    ( r3_orders_2(sK0,sK2,sK2) )).

cnf(u36,axiom,
    ( ~ r3_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X2)
    | v2_struct_0(X0) )).

cnf(u134,negated_conjecture,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK1),u1_struct_0(sK0))
    | r1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

cnf(u129,negated_conjecture,
    ( m1_subset_1(sK3(sK0,sK2,sK2,sK2),u1_struct_0(sK0))
    | r1_yellow_0(sK0,k2_tarski(sK2,sK2)) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u15,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
    | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) )).

cnf(u38,axiom,
    ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X5)
    | ~ r1_orders_2(X0,X2,X5)
    | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5) )).

cnf(u44,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK2,sK2) )).

cnf(u47,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK1) )).

cnf(u148,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_yellow_0(sK0,k2_tarski(sK2,sK2))
    | r3_orders_2(sK0,sK3(sK0,sK2,sK2,sK2),sK3(sK0,sK2,sK2,sK2)) )).

cnf(u178,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_yellow_0(sK0,k2_tarski(sK1,sK1))
    | r3_orders_2(sK0,sK3(sK0,sK1,sK1,sK1),sK3(sK0,sK1,sK1,sK1)) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r3_orders_2(X0,X1,X1) )).

cnf(u22,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u20,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u19,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u239,negated_conjecture,
    ( sK1 = k10_lattice3(sK0,sK1,sK1) )).

cnf(u218,negated_conjecture,
    ( sK2 = k10_lattice3(sK0,sK2,sK2) )).

cnf(u16,negated_conjecture,
    ( k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2) )).

cnf(u17,negated_conjecture,
    ( sK1 != sK2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:57:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (31119)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.45  % (31126)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.45  % (31134)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (31126)Refutation not found, incomplete strategy% (31126)------------------------------
% 0.19/0.45  % (31126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (31126)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (31126)Memory used [KB]: 6012
% 0.19/0.45  % (31126)Time elapsed: 0.003 s
% 0.19/0.45  % (31126)------------------------------
% 0.19/0.45  % (31126)------------------------------
% 0.19/0.46  % (31134)Refutation not found, incomplete strategy% (31134)------------------------------
% 0.19/0.46  % (31134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (31134)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (31134)Memory used [KB]: 10618
% 0.19/0.46  % (31134)Time elapsed: 0.061 s
% 0.19/0.46  % (31134)------------------------------
% 0.19/0.46  % (31134)------------------------------
% 0.19/0.46  % (31128)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.46  % (31127)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.47  % (31115)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (31125)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.47  % (31127)Refutation not found, incomplete strategy% (31127)------------------------------
% 0.19/0.47  % (31127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (31127)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (31127)Memory used [KB]: 1791
% 0.19/0.47  % (31127)Time elapsed: 0.081 s
% 0.19/0.47  % (31127)------------------------------
% 0.19/0.47  % (31127)------------------------------
% 0.19/0.47  % (31124)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.47  % (31123)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.47  % (31124)Refutation not found, incomplete strategy% (31124)------------------------------
% 0.19/0.47  % (31124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (31124)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (31124)Memory used [KB]: 6012
% 0.19/0.47  % (31124)Time elapsed: 0.076 s
% 0.19/0.47  % (31124)------------------------------
% 0.19/0.47  % (31124)------------------------------
% 0.19/0.47  % (31121)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.47  % (31125)Refutation not found, incomplete strategy% (31125)------------------------------
% 0.19/0.47  % (31125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (31125)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (31125)Memory used [KB]: 10618
% 0.19/0.47  % (31125)Time elapsed: 0.077 s
% 0.19/0.47  % (31125)------------------------------
% 0.19/0.47  % (31125)------------------------------
% 0.19/0.47  % (31120)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.48  % (31122)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.48  % (31130)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.48  % (31132)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.48  % (31133)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.48  % (31118)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.48  % (31116)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.48  % (31115)Refutation not found, incomplete strategy% (31115)------------------------------
% 0.19/0.48  % (31115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (31115)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (31115)Memory used [KB]: 10618
% 0.19/0.48  % (31115)Time elapsed: 0.074 s
% 0.19/0.48  % (31115)------------------------------
% 0.19/0.48  % (31115)------------------------------
% 0.19/0.48  % (31114)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % (31117)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.49  % (31114)Refutation not found, incomplete strategy% (31114)------------------------------
% 0.19/0.49  % (31114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (31114)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (31114)Memory used [KB]: 6268
% 0.19/0.49  % (31114)Time elapsed: 0.100 s
% 0.19/0.49  % (31114)------------------------------
% 0.19/0.49  % (31114)------------------------------
% 0.19/0.50  % (31131)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.50  % (31116)Refutation not found, incomplete strategy% (31116)------------------------------
% 0.19/0.50  % (31116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (31116)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (31116)Memory used [KB]: 10874
% 0.19/0.50  % (31116)Time elapsed: 0.106 s
% 0.19/0.50  % (31116)------------------------------
% 0.19/0.50  % (31116)------------------------------
% 0.19/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.50  % (31131)# SZS output start Saturation.
% 0.19/0.50  cnf(u197,negated_conjecture,
% 0.19/0.50      r1_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 0.19/0.50  
% 0.19/0.50  cnf(u172,negated_conjecture,
% 0.19/0.50      r1_yellow_0(sK0,k2_tarski(sK2,sK2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u21,negated_conjecture,
% 0.19/0.50      v5_orders_2(sK0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u136,negated_conjecture,
% 0.19/0.50      r1_orders_2(sK0,sK1,sK3(sK0,sK1,sK1,sK1)) | r1_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 0.19/0.50  
% 0.19/0.50  cnf(u63,negated_conjecture,
% 0.19/0.50      r1_orders_2(sK0,sK1,sK1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u131,negated_conjecture,
% 0.19/0.50      r1_orders_2(sK0,sK2,sK3(sK0,sK2,sK2,sK2)) | r1_yellow_0(sK0,k2_tarski(sK2,sK2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u55,negated_conjecture,
% 0.19/0.50      r1_orders_2(sK0,sK2,sK2)).
% 0.19/0.50  
% 0.19/0.50  cnf(u112,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,X0,sK1),u1_struct_0(sK0)) | r1_yellow_0(sK0,k2_tarski(sK1,X0))).
% 0.19/0.50  
% 0.19/0.50  cnf(u115,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X1,sK1)) | r1_yellow_0(sK0,k2_tarski(sK1,X1))).
% 0.19/0.50  
% 0.19/0.50  cnf(u118,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X2,sK3(sK0,sK1,X2,sK1)) | r1_yellow_0(sK0,k2_tarski(sK1,X2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u121,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,X3,sK1),u1_struct_0(sK0)) | sK1 = k10_lattice3(sK0,sK1,X3)).
% 0.19/0.50  
% 0.19/0.50  cnf(u124,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK3(sK0,sK1,X4,sK1)) | sK1 = k10_lattice3(sK0,sK1,X4)).
% 0.19/0.50  
% 0.19/0.50  cnf(u127,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X5,sK1) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r1_orders_2(sK0,X5,sK3(sK0,sK1,X5,sK1)) | sK1 = k10_lattice3(sK0,sK1,X5)).
% 0.19/0.50  
% 0.19/0.50  cnf(u80,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK2,X0,sK2),u1_struct_0(sK0)) | r1_yellow_0(sK0,k2_tarski(sK2,X0))).
% 0.19/0.50  
% 0.19/0.50  cnf(u83,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK3(sK0,sK2,X1,sK2)) | r1_yellow_0(sK0,k2_tarski(sK2,X1))).
% 0.19/0.50  
% 0.19/0.50  cnf(u86,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X2,sK2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X2,sK3(sK0,sK2,X2,sK2)) | r1_yellow_0(sK0,k2_tarski(sK2,X2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u89,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X3,sK2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK2,X3,sK2),u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,sK2,X3)).
% 0.19/0.50  
% 0.19/0.50  cnf(u92,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK3(sK0,sK2,X4,sK2)) | sK2 = k10_lattice3(sK0,sK2,X4)).
% 0.19/0.50  
% 0.19/0.50  cnf(u95,negated_conjecture,
% 0.19/0.50      ~r1_orders_2(sK0,X5,sK2) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r1_orders_2(sK0,X5,sK3(sK0,sK2,X5,sK2)) | sK2 = k10_lattice3(sK0,sK2,X5)).
% 0.19/0.50  
% 0.19/0.50  cnf(u27,axiom,
% 0.19/0.50      ~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~v5_orders_2(X0) | r1_yellow_0(X0,k2_tarski(X1,X2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u31,axiom,
% 0.19/0.50      ~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~v5_orders_2(X0) | k10_lattice3(X0,X1,X2) = X3).
% 0.19/0.50  
% 0.19/0.50  cnf(u35,axiom,
% 0.19/0.50      ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2)).
% 0.19/0.50  
% 0.19/0.50  cnf(u30,axiom,
% 0.19/0.50      ~r1_orders_2(X0,X1,X3) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3).
% 0.19/0.50  
% 0.19/0.50  cnf(u29,axiom,
% 0.19/0.50      ~r1_orders_2(X0,X1,X3) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3).
% 0.19/0.50  
% 0.19/0.50  cnf(u28,axiom,
% 0.19/0.50      ~r1_orders_2(X0,X1,X3) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = X3).
% 0.19/0.50  
% 0.19/0.50  cnf(u26,axiom,
% 0.19/0.50      ~r1_orders_2(X0,X1,X3) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | r1_yellow_0(X0,k2_tarski(X1,X2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u25,axiom,
% 0.19/0.50      ~r1_orders_2(X0,X1,X3) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) | r1_yellow_0(X0,k2_tarski(X1,X2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u24,axiom,
% 0.19/0.50      ~r1_orders_2(X0,X1,X3) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) | r1_yellow_0(X0,k2_tarski(X1,X2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u56,negated_conjecture,
% 0.19/0.50      r3_orders_2(sK0,sK1,sK1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u48,negated_conjecture,
% 0.19/0.50      r3_orders_2(sK0,sK2,sK2)).
% 0.19/0.50  
% 0.19/0.50  cnf(u36,axiom,
% 0.19/0.50      ~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u134,negated_conjecture,
% 0.19/0.50      m1_subset_1(sK3(sK0,sK1,sK1,sK1),u1_struct_0(sK0)) | r1_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 0.19/0.50  
% 0.19/0.50  cnf(u129,negated_conjecture,
% 0.19/0.50      m1_subset_1(sK3(sK0,sK2,sK2,sK2),u1_struct_0(sK0)) | r1_yellow_0(sK0,k2_tarski(sK2,sK2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u18,negated_conjecture,
% 0.19/0.50      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.19/0.50  
% 0.19/0.50  cnf(u15,negated_conjecture,
% 0.19/0.50      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.19/0.50  
% 0.19/0.50  cnf(u37,axiom,
% 0.19/0.50      ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_yellow_0(X0,k2_tarski(X1,X2)) | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u38,axiom,
% 0.19/0.50      ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_yellow_0(X0,k2_tarski(X1,X2)) | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u39,axiom,
% 0.19/0.50      ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_yellow_0(X0,k2_tarski(X1,X2)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X5) | ~r1_orders_2(X0,X2,X5) | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)).
% 0.19/0.50  
% 0.19/0.50  cnf(u44,negated_conjecture,
% 0.19/0.50      ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK2,sK2)).
% 0.19/0.50  
% 0.19/0.50  cnf(u47,negated_conjecture,
% 0.19/0.50      ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,sK1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u148,negated_conjecture,
% 0.19/0.50      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,k2_tarski(sK2,sK2)) | r3_orders_2(sK0,sK3(sK0,sK2,sK2,sK2),sK3(sK0,sK2,sK2,sK2))).
% 0.19/0.50  
% 0.19/0.50  cnf(u178,negated_conjecture,
% 0.19/0.50      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,k2_tarski(sK1,sK1)) | r3_orders_2(sK0,sK3(sK0,sK1,sK1,sK1),sK3(sK0,sK1,sK1,sK1))).
% 0.19/0.50  
% 0.19/0.50  cnf(u34,axiom,
% 0.19/0.50      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u22,negated_conjecture,
% 0.19/0.50      l1_orders_2(sK0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u20,negated_conjecture,
% 0.19/0.50      v3_orders_2(sK0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u19,negated_conjecture,
% 0.19/0.50      ~v2_struct_0(sK0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u239,negated_conjecture,
% 0.19/0.50      sK1 = k10_lattice3(sK0,sK1,sK1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u218,negated_conjecture,
% 0.19/0.50      sK2 = k10_lattice3(sK0,sK2,sK2)).
% 0.19/0.50  
% 0.19/0.50  cnf(u16,negated_conjecture,
% 0.19/0.50      k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2)).
% 0.19/0.50  
% 0.19/0.50  cnf(u17,negated_conjecture,
% 0.19/0.50      sK1 != sK2).
% 0.19/0.50  
% 0.19/0.50  % (31131)# SZS output end Saturation.
% 0.19/0.50  % (31131)------------------------------
% 0.19/0.50  % (31131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (31131)Termination reason: Satisfiable
% 0.19/0.50  
% 0.19/0.50  % (31131)Memory used [KB]: 1663
% 0.19/0.50  % (31131)Time elapsed: 0.111 s
% 0.19/0.50  % (31131)------------------------------
% 0.19/0.50  % (31131)------------------------------
% 0.19/0.50  % (31113)Success in time 0.166 s
%------------------------------------------------------------------------------
