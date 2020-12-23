%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:00 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   43 (  43 expanded)
%              Number of leaves         :   43 (  43 expanded)
%              Depth                    :    0
%              Number of atoms          :  173 ( 173 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal clause size      :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u162,negated_conjecture,
    ( r2_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

cnf(u144,negated_conjecture,
    ( r2_yellow_0(sK0,k2_tarski(sK2,sK2)) )).

cnf(u18,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u116,negated_conjecture,
    ( r1_orders_2(sK0,sK3(sK0,sK2,sK2,sK2),sK3(sK0,sK2,sK2,sK2))
    | r2_yellow_0(sK0,k2_tarski(sK2,sK2)) )).

cnf(u109,negated_conjecture,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK1,sK1),sK1)
    | r2_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

cnf(u106,negated_conjecture,
    ( r1_orders_2(sK0,sK3(sK0,sK2,sK2,sK2),sK2)
    | r2_yellow_0(sK0,k2_tarski(sK2,sK2)) )).

cnf(u42,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u39,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2) )).

cnf(u96,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK1,X3,sK1),X3)
    | r2_yellow_0(sK0,k2_tarski(sK1,X3)) )).

cnf(u99,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK1,X4,sK1),sK1)
    | r2_yellow_0(sK0,k2_tarski(sK1,X4)) )).

cnf(u102,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,X5)
    | ~ m1_subset_1(X5,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,X5,sK1),u1_struct_0(sK0))
    | r2_yellow_0(sK0,k2_tarski(sK1,X5)) )).

cnf(u87,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK1,X0,sK1),X0)
    | sK1 = k11_lattice3(sK0,sK1,X0) )).

cnf(u90,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1)
    | sK1 = k11_lattice3(sK0,sK1,X1) )).

cnf(u93,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,X2,sK1),u1_struct_0(sK0))
    | sK1 = k11_lattice3(sK0,sK1,X2) )).

cnf(u47,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK2,X0,sK2),u1_struct_0(sK0))
    | r2_yellow_0(sK0,k2_tarski(sK2,X0)) )).

cnf(u52,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK2,X0,sK2),sK2)
    | r2_yellow_0(sK0,k2_tarski(sK2,X0)) )).

cnf(u57,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK2,X0,sK2),X0)
    | r2_yellow_0(sK0,k2_tarski(sK2,X0)) )).

cnf(u62,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK2,X0,sK2),u1_struct_0(sK0))
    | sK2 = k11_lattice3(sK0,sK2,X0) )).

cnf(u67,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK2,X0,sK2),sK2)
    | sK2 = k11_lattice3(sK0,sK2,X0) )).

cnf(u72,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,sK2,X0,sK2),X0)
    | sK2 = k11_lattice3(sK0,sK2,X0) )).

cnf(u25,axiom,
    ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ v5_orders_2(X0)
    | r2_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u29,axiom,
    ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ v5_orders_2(X0)
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u22,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
    | r2_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u23,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
    | r2_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u24,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
    | r2_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u26,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u27,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u28,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u112,negated_conjecture,
    ( m1_subset_1(sK3(sK0,sK1,sK1,sK1),u1_struct_0(sK0))
    | r2_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

cnf(u104,negated_conjecture,
    ( m1_subset_1(sK3(sK0,sK2,sK2,sK2),u1_struct_0(sK0))
    | r2_yellow_0(sK0,k2_tarski(sK2,sK2)) )).

cnf(u15,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u12,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u32,axiom,
    ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) )).

cnf(u33,axiom,
    ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X5,X1)
    | ~ r1_orders_2(X0,X5,X2)
    | r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2)) )).

cnf(u20,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | r1_orders_2(X0,X1,X1) )).

cnf(u19,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u17,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u16,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u195,negated_conjecture,
    ( sK1 = k11_lattice3(sK0,sK1,sK1) )).

cnf(u181,negated_conjecture,
    ( sK2 = k11_lattice3(sK0,sK2,sK2) )).

cnf(u13,negated_conjecture,
    ( k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2) )).

cnf(u14,negated_conjecture,
    ( sK1 != sK2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (15732)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.45  % (15745)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (15742)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (15734)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (15738)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.46  % (15738)Refutation not found, incomplete strategy% (15738)------------------------------
% 0.21/0.46  % (15738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (15738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (15738)Memory used [KB]: 10618
% 0.21/0.46  % (15738)Time elapsed: 0.076 s
% 0.21/0.46  % (15738)------------------------------
% 0.21/0.46  % (15738)------------------------------
% 0.21/0.46  % (15727)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (15735)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (15727)Refutation not found, incomplete strategy% (15727)------------------------------
% 0.21/0.47  % (15727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15727)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (15727)Memory used [KB]: 6268
% 0.21/0.47  % (15727)Time elapsed: 0.055 s
% 0.21/0.47  % (15727)------------------------------
% 0.21/0.47  % (15727)------------------------------
% 0.21/0.47  % (15728)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (15728)Refutation not found, incomplete strategy% (15728)------------------------------
% 0.21/0.47  % (15728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15728)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (15728)Memory used [KB]: 10618
% 0.21/0.47  % (15728)Time elapsed: 0.061 s
% 0.21/0.47  % (15728)------------------------------
% 0.21/0.47  % (15728)------------------------------
% 0.21/0.47  % (15747)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (15747)Refutation not found, incomplete strategy% (15747)------------------------------
% 0.21/0.47  % (15747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15731)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (15747)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (15747)Memory used [KB]: 10618
% 0.21/0.47  % (15747)Time elapsed: 0.064 s
% 0.21/0.47  % (15747)------------------------------
% 0.21/0.47  % (15747)------------------------------
% 0.21/0.48  % (15730)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (15739)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (15729)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (15737)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (15741)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (15740)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (15744)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (15733)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (15743)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (15736)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (15744)# SZS output start Saturation.
% 0.21/0.49  cnf(u162,negated_conjecture,
% 0.21/0.49      r2_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u144,negated_conjecture,
% 0.21/0.49      r2_yellow_0(sK0,k2_tarski(sK2,sK2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u18,negated_conjecture,
% 0.21/0.49      v5_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u116,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,sK3(sK0,sK2,sK2,sK2),sK3(sK0,sK2,sK2,sK2)) | r2_yellow_0(sK0,k2_tarski(sK2,sK2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u109,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,sK3(sK0,sK1,sK1,sK1),sK1) | r2_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u106,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,sK3(sK0,sK2,sK2,sK2),sK2) | r2_yellow_0(sK0,k2_tarski(sK2,sK2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u42,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,sK1,sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u39,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,sK2,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u96,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK1,X3,sK1),X3) | r2_yellow_0(sK0,k2_tarski(sK1,X3))).
% 0.21/0.49  
% 0.21/0.49  cnf(u99,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK1,X4,sK1),sK1) | r2_yellow_0(sK0,k2_tarski(sK1,X4))).
% 0.21/0.49  
% 0.21/0.49  cnf(u102,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK1,X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,X5,sK1),u1_struct_0(sK0)) | r2_yellow_0(sK0,k2_tarski(sK1,X5))).
% 0.21/0.49  
% 0.21/0.49  cnf(u87,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK1,X0,sK1),X0) | sK1 = k11_lattice3(sK0,sK1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u90,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK1,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK1,X1,sK1),sK1) | sK1 = k11_lattice3(sK0,sK1,X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u93,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,X2,sK1),u1_struct_0(sK0)) | sK1 = k11_lattice3(sK0,sK1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u47,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK2,X0,sK2),u1_struct_0(sK0)) | r2_yellow_0(sK0,k2_tarski(sK2,X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u52,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK2,X0,sK2),sK2) | r2_yellow_0(sK0,k2_tarski(sK2,X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u57,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK2,X0,sK2),X0) | r2_yellow_0(sK0,k2_tarski(sK2,X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u62,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK2,X0,sK2),u1_struct_0(sK0)) | sK2 = k11_lattice3(sK0,sK2,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u67,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK2,X0,sK2),sK2) | sK2 = k11_lattice3(sK0,sK2,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u72,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,sK2,X0,sK2),X0) | sK2 = k11_lattice3(sK0,sK2,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u25,axiom,
% 0.21/0.49      ~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~v5_orders_2(X0) | r2_yellow_0(X0,k2_tarski(X1,X2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u29,axiom,
% 0.21/0.49      ~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~v5_orders_2(X0) | k11_lattice3(X0,X1,X2) = X3).
% 0.21/0.49  
% 0.21/0.49  cnf(u22,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) | r2_yellow_0(X0,k2_tarski(X1,X2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u23,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) | r2_yellow_0(X0,k2_tarski(X1,X2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u24,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) | r2_yellow_0(X0,k2_tarski(X1,X2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u26,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = X3).
% 0.21/0.49  
% 0.21/0.49  cnf(u27,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3).
% 0.21/0.49  
% 0.21/0.49  cnf(u28,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) | k11_lattice3(X0,X1,X2) = X3).
% 0.21/0.49  
% 0.21/0.49  cnf(u112,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK3(sK0,sK1,sK1,sK1),u1_struct_0(sK0)) | r2_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u104,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK3(sK0,sK2,sK2,sK2),u1_struct_0(sK0)) | r2_yellow_0(sK0,k2_tarski(sK2,sK2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u15,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u12,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u32,axiom,
% 0.21/0.49      ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_yellow_0(X0,k2_tarski(X1,X2)) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u33,axiom,
% 0.21/0.49      ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_yellow_0(X0,k2_tarski(X1,X2)) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u34,axiom,
% 0.21/0.49      ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_yellow_0(X0,k2_tarski(X1,X2)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_orders_2(X0,X5,X1) | ~r1_orders_2(X0,X5,X2) | r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u20,axiom,
% 0.21/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u19,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u17,negated_conjecture,
% 0.21/0.49      v3_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u16,negated_conjecture,
% 0.21/0.49      ~v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u195,negated_conjecture,
% 0.21/0.49      sK1 = k11_lattice3(sK0,sK1,sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u181,negated_conjecture,
% 0.21/0.49      sK2 = k11_lattice3(sK0,sK2,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u13,negated_conjecture,
% 0.21/0.49      k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u14,negated_conjecture,
% 0.21/0.49      sK1 != sK2).
% 0.21/0.49  
% 0.21/0.49  % (15744)# SZS output end Saturation.
% 0.21/0.49  % (15744)------------------------------
% 0.21/0.49  % (15744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15744)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (15744)Memory used [KB]: 1663
% 0.21/0.49  % (15744)Time elapsed: 0.090 s
% 0.21/0.49  % (15744)------------------------------
% 0.21/0.49  % (15744)------------------------------
% 0.21/0.49  % (15729)Refutation not found, incomplete strategy% (15729)------------------------------
% 0.21/0.49  % (15729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15726)Success in time 0.138 s
%------------------------------------------------------------------------------
