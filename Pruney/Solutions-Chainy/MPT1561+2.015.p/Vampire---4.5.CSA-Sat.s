%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:09 EST 2020

% Result     : CounterSatisfiable 1.33s
% Output     : Saturation 1.33s
% Verified   : 
% Statistics : Number of clauses        :   52 (  52 expanded)
%              Number of leaves         :   52 (  52 expanded)
%              Depth                    :    0
%              Number of atoms          :  168 ( 168 expanded)
%              Number of equality atoms :   69 (  69 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u79,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | r2_hidden(sK2(sK0,X0,sK1),X0) )).

cnf(u83,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u50,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u81,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | r2_hidden(sK3(sK0,X0,sK1),X0) )).

cnf(u86,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u54,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X2,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u44,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u60,axiom,
    ( ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2 )).

cnf(u84,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u88,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X0 = X1 )).

cnf(u57,axiom,
    ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u53,axiom,
    ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u43,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u58,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X1)
    | v2_struct_0(X0) )).

cnf(u46,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u74,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0) )).

cnf(u96,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(sK2(sK0,X0,sK1),X0)
    | r1_orders_2(sK0,X1,sK1) )).

cnf(u99,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(sK3(sK0,X0,sK1),X0)
    | r1_orders_2(sK0,sK1,X1) )).

cnf(u102,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK1) )).

cnf(u105,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,X1) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | r1_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u55,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u61,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1)
    | v1_xboole_0(X0) )).

cnf(u45,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u49,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u59,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u69,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u42,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u64,axiom,
    ( r2_hidden(sK4(X0,X1),X1)
    | sK4(X0,X1) = X0
    | k1_tarski(X0) = X1 )).

cnf(u67,axiom,
    ( r2_hidden(X3,k1_tarski(X3)) )).

cnf(u250,axiom,
    ( ~ r2_hidden(sK4(X14,k1_tarski(X13)),k1_tarski(X13))
    | sK4(X14,k1_tarski(X13)) != X12
    | k1_tarski(X12) = k1_tarski(X13)
    | sK4(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14) )).

cnf(u65,axiom,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | sK4(X0,X1) != X0
    | k1_tarski(X0) = X1 )).

cnf(u68,axiom,
    ( ~ r2_hidden(X3,k1_tarski(X0))
    | X0 = X3 )).

cnf(u119,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | k1_tarski(X0) = k1_tarski(X1)
    | sK4(X0,k1_tarski(X1)) = X1 )).

cnf(u144,axiom,
    ( ~ r2_hidden(X4,k1_tarski(X3))
    | sK4(X2,k1_tarski(X3)) = X4
    | sK4(X2,k1_tarski(X3)) = X2
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u147,axiom,
    ( ~ r2_hidden(X13,k1_tarski(X12))
    | k1_tarski(X12) = k1_tarski(X13)
    | sK4(X11,k1_tarski(X12)) = sK4(X13,k1_tarski(X12))
    | sK4(X11,k1_tarski(X12)) = X11
    | k1_tarski(X12) = k1_tarski(X11) )).

cnf(u91,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u128,axiom,
    ( sK4(sK4(X1,k1_tarski(X2)),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k1_tarski(sK4(X1,k1_tarski(X2)))
    | sK4(X1,k1_tarski(X2)) = X1
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u145,axiom,
    ( sK4(X7,k1_tarski(X6)) = X7
    | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6))
    | sK4(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u75,axiom,
    ( sK4(X0,k1_tarski(X1)) = X0
    | sK4(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u75_001,axiom,
    ( sK4(X0,k1_tarski(X1)) = X0
    | sK4(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u145_002,axiom,
    ( sK4(X7,k1_tarski(X6)) = X7
    | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6))
    | sK4(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u145_003,axiom,
    ( sK4(X7,k1_tarski(X6)) = X7
    | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6))
    | sK4(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u140,axiom,
    ( k1_tarski(X5) = k1_tarski(sK4(X4,k1_tarski(X5)))
    | sK4(X4,k1_tarski(X5)) = X4
    | k1_tarski(X5) = k1_tarski(X4) )).

cnf(u48,axiom,
    ( k1_tarski(X0) = k2_tarski(X0,X0) )).

cnf(u208,axiom,
    ( sK4(X2,k1_tarski(X1)) != X0
    | sK4(X2,k1_tarski(X1)) = X2
    | sK4(X0,k1_tarski(X1)) = X0
    | k1_tarski(X1) = k1_tarski(X2)
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u206,axiom,
    ( sK4(X2,k1_tarski(X1)) != X0
    | sK4(X0,k1_tarski(X1)) = sK4(X2,k1_tarski(X1))
    | sK4(X2,k1_tarski(X1)) = X2
    | k1_tarski(X0) = k1_tarski(X1)
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u114,axiom,
    ( X0 != X1
    | sK4(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u120,axiom,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1)
    | sK4(X0,k1_tarski(X1)) = X0 )).

cnf(u93,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k1_tarski(sK1))
    | sK1 != k1_yellow_0(sK0,k1_tarski(sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (15471)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (15495)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (15466)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.49  % (15479)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.49  % (15495)Refutation not found, incomplete strategy% (15495)------------------------------
% 0.20/0.49  % (15495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15495)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15495)Memory used [KB]: 1663
% 0.20/0.49  % (15495)Time elapsed: 0.104 s
% 0.20/0.49  % (15495)------------------------------
% 0.20/0.49  % (15495)------------------------------
% 0.20/0.50  % (15474)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (15469)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (15483)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (15472)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (15482)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (15482)Refutation not found, incomplete strategy% (15482)------------------------------
% 0.20/0.51  % (15482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.51  % (15483)Refutation not found, incomplete strategy% (15483)------------------------------
% 1.22/0.51  % (15483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.51  % (15483)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.51  
% 1.22/0.51  % (15483)Memory used [KB]: 1663
% 1.22/0.51  % (15483)Time elapsed: 0.113 s
% 1.22/0.51  % (15483)------------------------------
% 1.22/0.51  % (15483)------------------------------
% 1.22/0.51  % (15480)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.22/0.52  % (15489)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.22/0.52  % (15490)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.22/0.52  % (15488)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.22/0.52  % (15485)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.22/0.52  % (15482)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (15482)Memory used [KB]: 10618
% 1.22/0.52  % (15482)Time elapsed: 0.085 s
% 1.22/0.52  % (15482)------------------------------
% 1.22/0.52  % (15482)------------------------------
% 1.22/0.52  % (15467)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.52  % (15473)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.22/0.52  % (15470)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.52  % (15477)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.22/0.52  % (15467)Refutation not found, incomplete strategy% (15467)------------------------------
% 1.22/0.52  % (15467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (15467)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (15467)Memory used [KB]: 1663
% 1.22/0.52  % (15467)Time elapsed: 0.116 s
% 1.22/0.52  % (15467)------------------------------
% 1.22/0.52  % (15467)------------------------------
% 1.22/0.52  % (15481)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.52  % (15487)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.22/0.53  % (15468)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.53  % (15491)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.22/0.53  % (15494)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.53  % (15491)Refutation not found, incomplete strategy% (15491)------------------------------
% 1.33/0.53  % (15491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (15491)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (15491)Memory used [KB]: 6268
% 1.33/0.53  % (15491)Time elapsed: 0.109 s
% 1.33/0.53  % (15491)------------------------------
% 1.33/0.53  % (15491)------------------------------
% 1.33/0.53  % (15494)Refutation not found, incomplete strategy% (15494)------------------------------
% 1.33/0.53  % (15494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (15494)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (15494)Memory used [KB]: 10746
% 1.33/0.53  % (15494)Time elapsed: 0.129 s
% 1.33/0.53  % (15494)------------------------------
% 1.33/0.53  % (15494)------------------------------
% 1.33/0.54  % SZS status CounterSatisfiable for theBenchmark
% 1.33/0.54  % (15493)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.54  % (15493)Refutation not found, incomplete strategy% (15493)------------------------------
% 1.33/0.54  % (15493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (15493)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (15493)Memory used [KB]: 6140
% 1.33/0.54  % (15493)Time elapsed: 0.139 s
% 1.33/0.54  % (15493)------------------------------
% 1.33/0.54  % (15493)------------------------------
% 1.33/0.54  % (15486)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.54  % (15492)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (15492)Refutation not found, incomplete strategy% (15492)------------------------------
% 1.33/0.54  % (15492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (15492)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (15492)Memory used [KB]: 6268
% 1.33/0.54  % (15492)Time elapsed: 0.138 s
% 1.33/0.54  % (15492)------------------------------
% 1.33/0.54  % (15492)------------------------------
% 1.33/0.54  % (15476)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.33/0.54  % (15473)# SZS output start Saturation.
% 1.33/0.54  cnf(u79,negated_conjecture,
% 1.33/0.54      r2_lattice3(sK0,X0,sK1) | r2_hidden(sK2(sK0,X0,sK1),X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u83,negated_conjecture,
% 1.33/0.54      r2_lattice3(sK0,X0,sK1) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))).
% 1.33/0.54  
% 1.33/0.54  cnf(u50,axiom,
% 1.33/0.54      ~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u81,negated_conjecture,
% 1.33/0.54      r1_lattice3(sK0,X0,sK1) | r2_hidden(sK3(sK0,X0,sK1),X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u86,negated_conjecture,
% 1.33/0.54      r1_lattice3(sK0,X0,sK1) | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0))).
% 1.33/0.54  
% 1.33/0.54  cnf(u54,axiom,
% 1.33/0.54      ~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u44,negated_conjecture,
% 1.33/0.54      v5_orders_2(sK0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u60,axiom,
% 1.33/0.54      ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2).
% 1.33/0.54  
% 1.33/0.54  cnf(u84,negated_conjecture,
% 1.33/0.54      r1_orders_2(sK0,sK1,sK1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u88,negated_conjecture,
% 1.33/0.54      ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | X0 = X1).
% 1.33/0.54  
% 1.33/0.54  cnf(u57,axiom,
% 1.33/0.54      ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u53,axiom,
% 1.33/0.54      ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u43,negated_conjecture,
% 1.33/0.54      v3_orders_2(sK0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u58,axiom,
% 1.33/0.54      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X1) | v2_struct_0(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u46,negated_conjecture,
% 1.33/0.54      m1_subset_1(sK1,u1_struct_0(sK0))).
% 1.33/0.54  
% 1.33/0.54  cnf(u74,negated_conjecture,
% 1.33/0.54      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u96,negated_conjecture,
% 1.33/0.54      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_hidden(sK2(sK0,X0,sK1),X0) | r1_orders_2(sK0,X1,sK1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u99,negated_conjecture,
% 1.33/0.54      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_hidden(sK3(sK0,X0,sK1),X0) | r1_orders_2(sK0,sK1,X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u102,negated_conjecture,
% 1.33/0.54      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u105,negated_conjecture,
% 1.33/0.54      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u52,axiom,
% 1.33/0.54      ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK2(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u56,axiom,
% 1.33/0.54      ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u51,axiom,
% 1.33/0.54      ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u55,axiom,
% 1.33/0.54      ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u61,axiom,
% 1.33/0.54      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u45,negated_conjecture,
% 1.33/0.54      l1_orders_2(sK0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u49,axiom,
% 1.33/0.54      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u59,axiom,
% 1.33/0.54      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u69,negated_conjecture,
% 1.33/0.54      l1_struct_0(sK0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u42,negated_conjecture,
% 1.33/0.54      ~v2_struct_0(sK0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u64,axiom,
% 1.33/0.54      r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) = X0 | k1_tarski(X0) = X1).
% 1.33/0.54  
% 1.33/0.54  cnf(u67,axiom,
% 1.33/0.54      r2_hidden(X3,k1_tarski(X3))).
% 1.33/0.54  
% 1.33/0.54  cnf(u250,axiom,
% 1.33/0.54      ~r2_hidden(sK4(X14,k1_tarski(X13)),k1_tarski(X13)) | sK4(X14,k1_tarski(X13)) != X12 | k1_tarski(X12) = k1_tarski(X13) | sK4(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14)).
% 1.33/0.54  
% 1.33/0.54  cnf(u65,axiom,
% 1.33/0.54      ~r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) != X0 | k1_tarski(X0) = X1).
% 1.33/0.54  
% 1.33/0.54  cnf(u68,axiom,
% 1.33/0.54      ~r2_hidden(X3,k1_tarski(X0)) | X0 = X3).
% 1.33/0.54  
% 1.33/0.54  cnf(u119,axiom,
% 1.33/0.54      ~r2_hidden(X0,k1_tarski(X1)) | k1_tarski(X0) = k1_tarski(X1) | sK4(X0,k1_tarski(X1)) = X1).
% 1.33/0.54  
% 1.33/0.54  cnf(u144,axiom,
% 1.33/0.54      ~r2_hidden(X4,k1_tarski(X3)) | sK4(X2,k1_tarski(X3)) = X4 | sK4(X2,k1_tarski(X3)) = X2 | k1_tarski(X3) = k1_tarski(X2)).
% 1.33/0.54  
% 1.33/0.54  cnf(u147,axiom,
% 1.33/0.54      ~r2_hidden(X13,k1_tarski(X12)) | k1_tarski(X12) = k1_tarski(X13) | sK4(X11,k1_tarski(X12)) = sK4(X13,k1_tarski(X12)) | sK4(X11,k1_tarski(X12)) = X11 | k1_tarski(X12) = k1_tarski(X11)).
% 1.33/0.54  
% 1.33/0.54  cnf(u91,negated_conjecture,
% 1.33/0.54      k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u128,axiom,
% 1.33/0.54      sK4(sK4(X1,k1_tarski(X2)),k1_tarski(X2)) = X2 | k1_tarski(X2) = k1_tarski(sK4(X1,k1_tarski(X2))) | sK4(X1,k1_tarski(X2)) = X1 | k1_tarski(X1) = k1_tarski(X2)).
% 1.33/0.54  
% 1.33/0.54  cnf(u145,axiom,
% 1.33/0.54      sK4(X7,k1_tarski(X6)) = X7 | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6)) | sK4(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 1.33/0.54  
% 1.33/0.54  cnf(u75,axiom,
% 1.33/0.54      sK4(X0,k1_tarski(X1)) = X0 | sK4(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u75,axiom,
% 1.33/0.54      sK4(X0,k1_tarski(X1)) = X0 | sK4(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u145,axiom,
% 1.33/0.54      sK4(X7,k1_tarski(X6)) = X7 | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6)) | sK4(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 1.33/0.54  
% 1.33/0.54  cnf(u145,axiom,
% 1.33/0.54      sK4(X7,k1_tarski(X6)) = X7 | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6)) | sK4(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 1.33/0.54  
% 1.33/0.54  cnf(u140,axiom,
% 1.33/0.54      k1_tarski(X5) = k1_tarski(sK4(X4,k1_tarski(X5))) | sK4(X4,k1_tarski(X5)) = X4 | k1_tarski(X5) = k1_tarski(X4)).
% 1.33/0.54  
% 1.33/0.54  cnf(u48,axiom,
% 1.33/0.54      k1_tarski(X0) = k2_tarski(X0,X0)).
% 1.33/0.54  
% 1.33/0.54  cnf(u208,axiom,
% 1.33/0.54      sK4(X2,k1_tarski(X1)) != X0 | sK4(X2,k1_tarski(X1)) = X2 | sK4(X0,k1_tarski(X1)) = X0 | k1_tarski(X1) = k1_tarski(X2) | k1_tarski(X0) = k1_tarski(X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u206,axiom,
% 1.33/0.54      sK4(X2,k1_tarski(X1)) != X0 | sK4(X0,k1_tarski(X1)) = sK4(X2,k1_tarski(X1)) | sK4(X2,k1_tarski(X1)) = X2 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X1) = k1_tarski(X2)).
% 1.33/0.54  
% 1.33/0.54  cnf(u114,axiom,
% 1.33/0.54      X0 != X1 | sK4(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 1.33/0.54  
% 1.33/0.54  cnf(u120,axiom,
% 1.33/0.54      X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK4(X0,k1_tarski(X1)) = X0).
% 1.33/0.54  
% 1.33/0.54  cnf(u93,negated_conjecture,
% 1.33/0.54      sK1 != k2_yellow_0(sK0,k1_tarski(sK1)) | sK1 != k1_yellow_0(sK0,k1_tarski(sK1))).
% 1.33/0.54  
% 1.33/0.54  % (15473)# SZS output end Saturation.
% 1.33/0.54  % (15473)------------------------------
% 1.33/0.54  % (15473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (15473)Termination reason: Satisfiable
% 1.33/0.54  
% 1.33/0.54  % (15473)Memory used [KB]: 1791
% 1.33/0.54  % (15473)Time elapsed: 0.100 s
% 1.33/0.54  % (15473)------------------------------
% 1.33/0.54  % (15473)------------------------------
% 1.33/0.54  % (15470)Refutation not found, incomplete strategy% (15470)------------------------------
% 1.33/0.54  % (15470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (15470)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (15470)Memory used [KB]: 1791
% 1.33/0.54  % (15470)Time elapsed: 0.121 s
% 1.33/0.54  % (15470)------------------------------
% 1.33/0.54  % (15470)------------------------------
% 1.33/0.54  % (15465)Success in time 0.181 s
%------------------------------------------------------------------------------
