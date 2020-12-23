%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:02 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   73 (  73 expanded)
%              Number of leaves         :   73 (  73 expanded)
%              Depth                    :    0
%              Number of atoms          :  179 ( 179 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u65,negated_conjecture,
    ( sP1(sK4,sK4,sK2,sK4) )).

cnf(u64,negated_conjecture,
    ( sP1(sK3,sK4,sK2,sK4) )).

cnf(u63,negated_conjecture,
    ( sP1(sK4,sK4,sK2,sK3) )).

cnf(u62,negated_conjecture,
    ( sP1(sK3,sK4,sK2,sK3) )).

cnf(u61,negated_conjecture,
    ( sP1(sK4,sK3,sK2,sK4) )).

cnf(u60,negated_conjecture,
    ( sP1(sK3,sK3,sK2,sK4) )).

cnf(u59,negated_conjecture,
    ( sP1(sK4,sK3,sK2,sK3) )).

cnf(u58,negated_conjecture,
    ( sP1(sK3,sK3,sK2,sK3) )).

cnf(u34,axiom,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r2_lattice3(X2,k2_tarski(X3,X1),X0)
    | r1_orders_2(X2,X3,X0) )).

cnf(u35,axiom,
    ( ~ sP1(X0,X1,X2,X3)
    | ~ r2_lattice3(X2,k2_tarski(X3,X1),X0)
    | r1_orders_2(X2,X1,X0) )).

cnf(u54,negated_conjecture,
    ( sP0(sK4,sK4,sK2,sK4) )).

cnf(u53,negated_conjecture,
    ( sP0(sK4,sK3,sK2,sK4) )).

cnf(u52,negated_conjecture,
    ( sP0(sK4,sK4,sK2,sK3) )).

cnf(u51,negated_conjecture,
    ( sP0(sK4,sK3,sK2,sK3) )).

cnf(u50,negated_conjecture,
    ( sP0(sK3,sK4,sK2,sK4) )).

cnf(u49,negated_conjecture,
    ( sP0(sK3,sK3,sK2,sK4) )).

cnf(u48,negated_conjecture,
    ( sP0(sK3,sK4,sK2,sK3) )).

cnf(u47,negated_conjecture,
    ( sP0(sK3,sK3,sK2,sK3) )).

cnf(u36,axiom,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_lattice3(X2,k2_tarski(X3,X0),X1)
    | r1_orders_2(X2,X1,X3) )).

cnf(u37,axiom,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_lattice3(X2,k2_tarski(X3,X0),X1)
    | r1_orders_2(X2,X1,X0) )).

cnf(u81,negated_conjecture,
    ( r2_lattice3(sK2,k2_tarski(sK3,sK3),sK4) )).

cnf(u103,negated_conjecture,
    ( ~ r2_lattice3(sK2,k2_tarski(sK4,sK4),sK4)
    | r1_orders_2(sK2,sK4,sK4) )).

cnf(u101,negated_conjecture,
    ( ~ r2_lattice3(sK2,k2_tarski(sK4,sK4),sK3)
    | r1_orders_2(sK2,sK4,sK3) )).

cnf(u99,negated_conjecture,
    ( ~ r2_lattice3(sK2,k2_tarski(sK3,sK4),sK4)
    | r1_orders_2(sK2,sK4,sK4) )).

cnf(u97,negated_conjecture,
    ( ~ r2_lattice3(sK2,k2_tarski(sK3,sK4),sK3)
    | r1_orders_2(sK2,sK4,sK3) )).

cnf(u98,negated_conjecture,
    ( ~ r2_lattice3(sK2,k2_tarski(sK3,sK4),sK3)
    | r1_orders_2(sK2,sK3,sK3) )).

cnf(u96,negated_conjecture,
    ( ~ r2_lattice3(sK2,k2_tarski(sK4,sK3),sK4)
    | r1_orders_2(sK2,sK4,sK4) )).

cnf(u93,negated_conjecture,
    ( ~ r2_lattice3(sK2,k2_tarski(sK4,sK3),sK3)
    | r1_orders_2(sK2,sK3,sK3) )).

cnf(u94,negated_conjecture,
    ( ~ r2_lattice3(sK2,k2_tarski(sK4,sK3),sK3)
    | r1_orders_2(sK2,sK4,sK3) )).

cnf(u89,negated_conjecture,
    ( ~ r2_lattice3(sK2,k2_tarski(sK3,sK3),sK3)
    | r1_orders_2(sK2,sK3,sK3) )).

cnf(u74,negated_conjecture,
    ( ~ r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_lattice3(sK2,X0,X2) )).

cnf(u77,negated_conjecture,
    ( r1_lattice3(sK2,k2_tarski(sK4,sK4),sK3) )).

cnf(u70,negated_conjecture,
    ( ~ r1_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | r1_lattice3(sK2,X0,X2) )).

cnf(u87,negated_conjecture,
    ( ~ r1_lattice3(sK2,k2_tarski(sK4,sK4),sK4)
    | r1_orders_2(sK2,sK4,sK4) )).

cnf(u83,negated_conjecture,
    ( ~ r1_lattice3(sK2,k2_tarski(sK3,sK4),sK4)
    | r1_orders_2(sK2,sK4,sK4) )).

cnf(u84,negated_conjecture,
    ( ~ r1_lattice3(sK2,k2_tarski(sK3,sK4),sK4)
    | r1_orders_2(sK2,sK4,sK3) )).

cnf(u80,negated_conjecture,
    ( ~ r1_lattice3(sK2,k2_tarski(sK3,sK4),sK3)
    | r1_orders_2(sK2,sK3,sK3) )).

cnf(u75,negated_conjecture,
    ( ~ r1_lattice3(sK2,k2_tarski(sK4,sK3),sK4)
    | r1_orders_2(sK2,sK4,sK3) )).

cnf(u76,negated_conjecture,
    ( ~ r1_lattice3(sK2,k2_tarski(sK4,sK3),sK4)
    | r1_orders_2(sK2,sK4,sK4) )).

cnf(u71,negated_conjecture,
    ( ~ r1_lattice3(sK2,k2_tarski(sK4,sK3),sK3)
    | r1_orders_2(sK2,sK3,sK3) )).

cnf(u67,negated_conjecture,
    ( ~ r1_lattice3(sK2,k2_tarski(sK3,sK3),sK4)
    | r1_orders_2(sK2,sK4,sK3) )).

cnf(u56,negated_conjecture,
    ( ~ r1_lattice3(sK2,k2_tarski(sK3,sK3),sK3)
    | r1_orders_2(sK2,sK3,sK3) )).

cnf(u32,negated_conjecture,
    ( r1_orders_2(sK2,sK3,sK4) )).

cnf(u136,negated_conjecture,
    ( ~ r1_orders_2(sK2,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_lattice3(sK2,k2_tarski(X0,sK4),sK3) )).

cnf(u132,negated_conjecture,
    ( ~ r1_orders_2(sK2,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_lattice3(sK2,k2_tarski(sK3,sK3),X0) )).

cnf(u140,negated_conjecture,
    ( ~ r1_orders_2(sK2,X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_lattice3(sK2,k2_tarski(X0,sK3),sK4) )).

cnf(u130,negated_conjecture,
    ( ~ r1_orders_2(sK2,X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_lattice3(sK2,k2_tarski(sK4,sK4),X0) )).

cnf(u78,negated_conjecture,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_lattice3(sK2,k2_tarski(X2,X1),X0) )).

cnf(u82,negated_conjecture,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_lattice3(sK2,k2_tarski(X2,X0),X1) )).

cnf(u29,negated_conjecture,
    ( l1_orders_2(sK2) )).

cnf(u38,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP0(X3,X1,X0,X2) )).

cnf(u40,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sP1(X1,X3,X0,X2) )).

cnf(u39,axiom,
    ( ~ l1_orders_2(X0)
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_lattice3(X0,k2_tarski(X2,X3),X1) )).

cnf(u41,axiom,
    ( ~ l1_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_lattice3(X0,k2_tarski(X2,X3),X1) )).

cnf(u28,negated_conjecture,
    ( v4_orders_2(sK2) )).

cnf(u42,axiom,
    ( ~ v4_orders_2(X0)
    | ~ r1_lattice3(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X3,X1) )).

cnf(u43,axiom,
    ( ~ v4_orders_2(X0)
    | ~ r2_lattice3(X0,X3,X1)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X3,X2) )).

cnf(u31,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) )).

cnf(u30,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) )).

cnf(u176,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sP1(X1,sK4,sK2,sK4) )).

cnf(u175,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | sP1(X0,sK4,sK2,sK3) )).

cnf(u166,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sP1(X1,sK3,sK2,sK4) )).

cnf(u165,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | sP1(X0,sK3,sK2,sK3) )).

cnf(u156,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sP0(sK4,X1,sK2,sK4) )).

cnf(u155,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | sP0(sK4,X0,sK2,sK3) )).

cnf(u146,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sP0(sK3,X1,sK2,sK4) )).

cnf(u145,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | sP0(sK3,X0,sK2,sK3) )).

cnf(u128,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | sP1(X3,sK4,sK2,X2) )).

cnf(u127,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sP1(X1,sK3,sK2,X0) )).

cnf(u118,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | sP0(sK4,X3,sK2,X2) )).

cnf(u117,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sP0(sK3,X1,sK2,X0) )).

cnf(u66,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | sP1(X2,X0,sK2,X1) )).

cnf(u55,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | sP0(X0,X2,sK2,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:59:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (23196)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % (23200)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (23207)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.48  % (23207)Refutation not found, incomplete strategy% (23207)------------------------------
% 0.22/0.48  % (23207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23207)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (23207)Memory used [KB]: 895
% 0.22/0.48  % (23207)Time elapsed: 0.062 s
% 0.22/0.48  % (23207)------------------------------
% 0.22/0.48  % (23207)------------------------------
% 0.22/0.49  % (23197)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (23209)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.22/0.49  % (23209)Refutation not found, incomplete strategy% (23209)------------------------------
% 0.22/0.49  % (23209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (23202)WARNING: option uwaf not known.
% 0.22/0.49  % (23202)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.49  % (23209)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (23209)Memory used [KB]: 9850
% 0.22/0.49  % (23209)Time elapsed: 0.065 s
% 0.22/0.49  % (23209)------------------------------
% 0.22/0.49  % (23209)------------------------------
% 0.22/0.49  % (23205)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (23202)Refutation not found, incomplete strategy% (23202)------------------------------
% 0.22/0.49  % (23202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (23202)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (23202)Memory used [KB]: 895
% 0.22/0.49  % (23202)Time elapsed: 0.062 s
% 0.22/0.49  % (23202)------------------------------
% 0.22/0.49  % (23202)------------------------------
% 0.22/0.49  % (23195)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.49  % (23204)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.50  % (23194)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.50  % (23195)Refutation not found, incomplete strategy% (23195)------------------------------
% 0.22/0.50  % (23195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (23195)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (23195)Memory used [KB]: 9850
% 0.22/0.50  % (23195)Time elapsed: 0.083 s
% 0.22/0.50  % (23195)------------------------------
% 0.22/0.50  % (23195)------------------------------
% 0.22/0.50  % (23192)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (23210)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (23192)Refutation not found, incomplete strategy% (23192)------------------------------
% 0.22/0.50  % (23192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (23192)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (23192)Memory used [KB]: 5373
% 0.22/0.50  % (23192)Time elapsed: 0.083 s
% 0.22/0.50  % (23192)------------------------------
% 0.22/0.50  % (23192)------------------------------
% 0.22/0.50  % (23197)Refutation not found, incomplete strategy% (23197)------------------------------
% 0.22/0.50  % (23197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (23197)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (23197)Memory used [KB]: 895
% 0.22/0.50  % (23197)Time elapsed: 0.057 s
% 0.22/0.50  % (23197)------------------------------
% 0.22/0.50  % (23197)------------------------------
% 0.22/0.51  % (23203)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.51  % (23212)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.22/0.51  % (23208)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.51  % (23208)Refutation not found, incomplete strategy% (23208)------------------------------
% 0.22/0.51  % (23208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23208)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23208)Memory used [KB]: 5373
% 0.22/0.51  % (23208)Time elapsed: 0.096 s
% 0.22/0.51  % (23208)------------------------------
% 0.22/0.51  % (23208)------------------------------
% 0.22/0.51  % (23206)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (23212)# SZS output start Saturation.
% 0.22/0.51  cnf(u65,negated_conjecture,
% 0.22/0.51      sP1(sK4,sK4,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u64,negated_conjecture,
% 0.22/0.51      sP1(sK3,sK4,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u63,negated_conjecture,
% 0.22/0.51      sP1(sK4,sK4,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u62,negated_conjecture,
% 0.22/0.51      sP1(sK3,sK4,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u61,negated_conjecture,
% 0.22/0.51      sP1(sK4,sK3,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u60,negated_conjecture,
% 0.22/0.51      sP1(sK3,sK3,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u59,negated_conjecture,
% 0.22/0.51      sP1(sK4,sK3,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u58,negated_conjecture,
% 0.22/0.51      sP1(sK3,sK3,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u34,axiom,
% 0.22/0.51      ~sP1(X0,X1,X2,X3) | ~r2_lattice3(X2,k2_tarski(X3,X1),X0) | r1_orders_2(X2,X3,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u35,axiom,
% 0.22/0.51      ~sP1(X0,X1,X2,X3) | ~r2_lattice3(X2,k2_tarski(X3,X1),X0) | r1_orders_2(X2,X1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u54,negated_conjecture,
% 0.22/0.51      sP0(sK4,sK4,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u53,negated_conjecture,
% 0.22/0.51      sP0(sK4,sK3,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u52,negated_conjecture,
% 0.22/0.51      sP0(sK4,sK4,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u51,negated_conjecture,
% 0.22/0.51      sP0(sK4,sK3,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u50,negated_conjecture,
% 0.22/0.51      sP0(sK3,sK4,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u49,negated_conjecture,
% 0.22/0.51      sP0(sK3,sK3,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u48,negated_conjecture,
% 0.22/0.51      sP0(sK3,sK4,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u47,negated_conjecture,
% 0.22/0.51      sP0(sK3,sK3,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u36,axiom,
% 0.22/0.51      ~sP0(X0,X1,X2,X3) | ~r1_lattice3(X2,k2_tarski(X3,X0),X1) | r1_orders_2(X2,X1,X3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u37,axiom,
% 0.22/0.51      ~sP0(X0,X1,X2,X3) | ~r1_lattice3(X2,k2_tarski(X3,X0),X1) | r1_orders_2(X2,X1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u81,negated_conjecture,
% 0.22/0.51      r2_lattice3(sK2,k2_tarski(sK3,sK3),sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u103,negated_conjecture,
% 0.22/0.51      ~r2_lattice3(sK2,k2_tarski(sK4,sK4),sK4) | r1_orders_2(sK2,sK4,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u101,negated_conjecture,
% 0.22/0.51      ~r2_lattice3(sK2,k2_tarski(sK4,sK4),sK3) | r1_orders_2(sK2,sK4,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u99,negated_conjecture,
% 0.22/0.51      ~r2_lattice3(sK2,k2_tarski(sK3,sK4),sK4) | r1_orders_2(sK2,sK4,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u97,negated_conjecture,
% 0.22/0.51      ~r2_lattice3(sK2,k2_tarski(sK3,sK4),sK3) | r1_orders_2(sK2,sK4,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u98,negated_conjecture,
% 0.22/0.51      ~r2_lattice3(sK2,k2_tarski(sK3,sK4),sK3) | r1_orders_2(sK2,sK3,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u96,negated_conjecture,
% 0.22/0.51      ~r2_lattice3(sK2,k2_tarski(sK4,sK3),sK4) | r1_orders_2(sK2,sK4,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u93,negated_conjecture,
% 0.22/0.51      ~r2_lattice3(sK2,k2_tarski(sK4,sK3),sK3) | r1_orders_2(sK2,sK3,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u94,negated_conjecture,
% 0.22/0.51      ~r2_lattice3(sK2,k2_tarski(sK4,sK3),sK3) | r1_orders_2(sK2,sK4,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u89,negated_conjecture,
% 0.22/0.51      ~r2_lattice3(sK2,k2_tarski(sK3,sK3),sK3) | r1_orders_2(sK2,sK3,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u74,negated_conjecture,
% 0.22/0.51      ~r2_lattice3(sK2,X0,X1) | ~r1_orders_2(sK2,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r2_lattice3(sK2,X0,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u77,negated_conjecture,
% 0.22/0.51      r1_lattice3(sK2,k2_tarski(sK4,sK4),sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u70,negated_conjecture,
% 0.22/0.51      ~r1_lattice3(sK2,X0,X1) | ~r1_orders_2(sK2,X2,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | r1_lattice3(sK2,X0,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u87,negated_conjecture,
% 0.22/0.51      ~r1_lattice3(sK2,k2_tarski(sK4,sK4),sK4) | r1_orders_2(sK2,sK4,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u83,negated_conjecture,
% 0.22/0.51      ~r1_lattice3(sK2,k2_tarski(sK3,sK4),sK4) | r1_orders_2(sK2,sK4,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u84,negated_conjecture,
% 0.22/0.51      ~r1_lattice3(sK2,k2_tarski(sK3,sK4),sK4) | r1_orders_2(sK2,sK4,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u80,negated_conjecture,
% 0.22/0.51      ~r1_lattice3(sK2,k2_tarski(sK3,sK4),sK3) | r1_orders_2(sK2,sK3,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u75,negated_conjecture,
% 0.22/0.51      ~r1_lattice3(sK2,k2_tarski(sK4,sK3),sK4) | r1_orders_2(sK2,sK4,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u76,negated_conjecture,
% 0.22/0.51      ~r1_lattice3(sK2,k2_tarski(sK4,sK3),sK4) | r1_orders_2(sK2,sK4,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u71,negated_conjecture,
% 0.22/0.51      ~r1_lattice3(sK2,k2_tarski(sK4,sK3),sK3) | r1_orders_2(sK2,sK3,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u67,negated_conjecture,
% 0.22/0.51      ~r1_lattice3(sK2,k2_tarski(sK3,sK3),sK4) | r1_orders_2(sK2,sK4,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u56,negated_conjecture,
% 0.22/0.51      ~r1_lattice3(sK2,k2_tarski(sK3,sK3),sK3) | r1_orders_2(sK2,sK3,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u32,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK2,sK3,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u136,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK2,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_lattice3(sK2,k2_tarski(X0,sK4),sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u132,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK2,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_lattice3(sK2,k2_tarski(sK3,sK3),X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u140,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK2,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_lattice3(sK2,k2_tarski(X0,sK3),sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u130,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK2,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_lattice3(sK2,k2_tarski(sK4,sK4),X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u78,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK2,X0,X1) | ~r1_orders_2(sK2,X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_lattice3(sK2,k2_tarski(X2,X1),X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u82,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK2,X0,X1) | ~r1_orders_2(sK2,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r2_lattice3(sK2,k2_tarski(X2,X0),X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP0(X3,X1,X0,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u40,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP1(X1,X3,X0,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u39,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattice3(X0,k2_tarski(X2,X3),X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u41,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_lattice3(X0,k2_tarski(X2,X3),X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u28,negated_conjecture,
% 0.22/0.51      v4_orders_2(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u42,axiom,
% 0.22/0.51      ~v4_orders_2(X0) | ~r1_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X3,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u43,axiom,
% 0.22/0.51      ~v4_orders_2(X0) | ~r2_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X3,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u31,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u30,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK3,u1_struct_0(sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u176,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(sK2)) | sP1(X1,sK4,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u175,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(sK2)) | sP1(X0,sK4,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u166,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(sK2)) | sP1(X1,sK3,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u165,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(sK2)) | sP1(X0,sK3,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u156,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(sK4,X1,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u155,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(sK2)) | sP0(sK4,X0,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u146,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(sK3,X1,sK2,sK4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u145,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(sK2)) | sP0(sK3,X0,sK2,sK3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u128,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK2)) | sP1(X3,sK4,sK2,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u127,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | sP1(X1,sK3,sK2,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u118,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X2,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK2)) | sP0(sK4,X3,sK2,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u117,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(sK3,X1,sK2,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u66,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | sP1(X2,X0,sK2,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u55,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | sP0(X0,X2,sK2,X1)).
% 0.22/0.51  
% 0.22/0.51  % (23212)# SZS output end Saturation.
% 0.22/0.51  % (23212)------------------------------
% 0.22/0.51  % (23212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23212)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (23212)Memory used [KB]: 5500
% 0.22/0.51  % (23212)Time elapsed: 0.099 s
% 0.22/0.51  % (23212)------------------------------
% 0.22/0.51  % (23212)------------------------------
% 0.22/0.51  % (23193)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.51  % (23191)Success in time 0.152 s
%------------------------------------------------------------------------------
