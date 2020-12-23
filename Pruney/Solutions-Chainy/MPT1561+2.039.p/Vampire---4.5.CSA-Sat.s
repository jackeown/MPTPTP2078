%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:13 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   41 (  41 expanded)
%              Number of leaves         :   41 (  41 expanded)
%              Depth                    :    0
%              Number of atoms          :  125 ( 125 expanded)
%              Number of equality atoms :   67 (  67 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u64,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | r2_hidden(sK2(sK0,X0,sK1),X0) )).

cnf(u66,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u40,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X2,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u67,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u43,axiom,
    ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u34,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u44,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X1)
    | v2_struct_0(X0) )).

cnf(u36,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u59,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0) )).

% (14883)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
cnf(u75,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(sK2(sK0,X0,sK1),X0)
    | r1_orders_2(sK0,sK1,X1) )).

% (14882)Refutation not found, incomplete strategy% (14882)------------------------------
% (14882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14882)Termination reason: Refutation not found, incomplete strategy

% (14882)Memory used [KB]: 1663
% (14882)Time elapsed: 0.114 s
% (14882)------------------------------
% (14882)------------------------------
cnf(u78,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,X1) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | r1_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1)
    | v1_xboole_0(X0) )).

cnf(u35,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u39,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u45,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u54,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u33,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u49,axiom,
    ( r2_hidden(sK3(X0,X1),X1)
    | sK3(X0,X1) = X0
    | k1_tarski(X0) = X1 )).

cnf(u52,axiom,
    ( r2_hidden(X3,k1_tarski(X3)) )).

cnf(u219,axiom,
    ( ~ r2_hidden(sK3(X14,k1_tarski(X13)),k1_tarski(X13))
    | sK3(X14,k1_tarski(X13)) != X12
    | k1_tarski(X12) = k1_tarski(X13)
    | sK3(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14) )).

cnf(u50,axiom,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | sK3(X0,X1) != X0
    | k1_tarski(X0) = X1 )).

cnf(u53,axiom,
    ( ~ r2_hidden(X3,k1_tarski(X0))
    | X0 = X3 )).

cnf(u90,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | k1_tarski(X0) = k1_tarski(X1)
    | sK3(X0,k1_tarski(X1)) = X1 )).

cnf(u113,axiom,
    ( ~ r2_hidden(X4,k1_tarski(X3))
    | sK3(X2,k1_tarski(X3)) = X4
    | sK3(X2,k1_tarski(X3)) = X2
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u116,axiom,
    ( ~ r2_hidden(X13,k1_tarski(X12))
    | k1_tarski(X12) = k1_tarski(X13)
    | sK3(X11,k1_tarski(X12)) = sK3(X13,k1_tarski(X12))
    | sK3(X11,k1_tarski(X12)) = X11
    | k1_tarski(X12) = k1_tarski(X11) )).

cnf(u70,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u97,axiom,
    ( sK3(sK3(X1,k1_tarski(X2)),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k1_tarski(sK3(X1,k1_tarski(X2)))
    | sK3(X1,k1_tarski(X2)) = X1
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u114,axiom,
    ( sK3(X7,k1_tarski(X6)) = X7
    | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6))
    | sK3(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u60,axiom,
    ( sK3(X0,k1_tarski(X1)) = X0
    | sK3(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u60_001,axiom,
    ( sK3(X0,k1_tarski(X1)) = X0
    | sK3(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u114_002,axiom,
    ( sK3(X7,k1_tarski(X6)) = X7
    | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6))
    | sK3(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u114_003,axiom,
    ( sK3(X7,k1_tarski(X6)) = X7
    | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6))
    | sK3(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u109,axiom,
    ( k1_tarski(X5) = k1_tarski(sK3(X4,k1_tarski(X5)))
    | sK3(X4,k1_tarski(X5)) = X4
    | k1_tarski(X5) = k1_tarski(X4) )).

cnf(u38,axiom,
    ( k1_tarski(X0) = k2_tarski(X0,X0) )).

cnf(u177,axiom,
    ( sK3(X2,k1_tarski(X1)) != X0
    | sK3(X2,k1_tarski(X1)) = X2
    | sK3(X0,k1_tarski(X1)) = X0
    | k1_tarski(X1) = k1_tarski(X2)
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u175,axiom,
    ( sK3(X2,k1_tarski(X1)) != X0
    | sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1))
    | sK3(X2,k1_tarski(X1)) = X2
    | k1_tarski(X0) = k1_tarski(X1)
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u85,axiom,
    ( X0 != X1
    | sK3(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u91,axiom,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1)
    | sK3(X0,k1_tarski(X1)) = X0 )).

cnf(u72,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k1_tarski(sK1))
    | sK1 != k1_yellow_0(sK0,k1_tarski(sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:49:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (14903)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.50  % (14886)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (14894)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (14888)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (14885)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (14904)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (14893)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (14910)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (14910)Refutation not found, incomplete strategy% (14910)------------------------------
% 0.22/0.52  % (14910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14910)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14910)Memory used [KB]: 1663
% 0.22/0.52  % (14910)Time elapsed: 0.001 s
% 0.22/0.52  % (14910)------------------------------
% 0.22/0.52  % (14910)------------------------------
% 0.22/0.52  % (14893)Refutation not found, incomplete strategy% (14893)------------------------------
% 0.22/0.52  % (14893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14893)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14893)Memory used [KB]: 10618
% 0.22/0.52  % (14893)Time elapsed: 0.109 s
% 0.22/0.52  % (14893)------------------------------
% 0.22/0.52  % (14893)------------------------------
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (14902)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (14895)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (14896)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (14882)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (14888)# SZS output start Saturation.
% 0.22/0.53  cnf(u64,negated_conjecture,
% 0.22/0.53      r1_lattice3(sK0,X0,sK1) | r2_hidden(sK2(sK0,X0,sK1),X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u66,negated_conjecture,
% 0.22/0.53      r1_lattice3(sK0,X0,sK1) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u40,axiom,
% 0.22/0.53      ~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u67,negated_conjecture,
% 0.22/0.53      r1_orders_2(sK0,sK1,sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u43,axiom,
% 0.22/0.53      ~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u34,negated_conjecture,
% 0.22/0.53      v3_orders_2(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u44,axiom,
% 0.22/0.53      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X1) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u36,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u59,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 0.22/0.53  
% 0.22/0.53  % (14883)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  cnf(u75,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_hidden(sK2(sK0,X0,sK1),X0) | r1_orders_2(sK0,sK1,X1)).
% 0.22/0.53  
% 0.22/0.53  % (14882)Refutation not found, incomplete strategy% (14882)------------------------------
% 0.22/0.53  % (14882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14882)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14882)Memory used [KB]: 1663
% 0.22/0.53  % (14882)Time elapsed: 0.114 s
% 0.22/0.53  % (14882)------------------------------
% 0.22/0.53  % (14882)------------------------------
% 0.22/0.53  cnf(u78,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u42,axiom,
% 0.22/0.53      ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK2(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u41,axiom,
% 0.22/0.53      ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u46,axiom,
% 0.22/0.53      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u35,negated_conjecture,
% 0.22/0.53      l1_orders_2(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u39,axiom,
% 0.22/0.53      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u45,axiom,
% 0.22/0.53      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u54,negated_conjecture,
% 0.22/0.53      l1_struct_0(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u33,negated_conjecture,
% 0.22/0.53      ~v2_struct_0(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u49,axiom,
% 0.22/0.53      r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) = X0 | k1_tarski(X0) = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u52,axiom,
% 0.22/0.53      r2_hidden(X3,k1_tarski(X3))).
% 0.22/0.53  
% 0.22/0.53  cnf(u219,axiom,
% 0.22/0.53      ~r2_hidden(sK3(X14,k1_tarski(X13)),k1_tarski(X13)) | sK3(X14,k1_tarski(X13)) != X12 | k1_tarski(X12) = k1_tarski(X13) | sK3(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14)).
% 0.22/0.53  
% 0.22/0.53  cnf(u50,axiom,
% 0.22/0.53      ~r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) != X0 | k1_tarski(X0) = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u53,axiom,
% 0.22/0.53      ~r2_hidden(X3,k1_tarski(X0)) | X0 = X3).
% 0.22/0.53  
% 0.22/0.53  cnf(u90,axiom,
% 0.22/0.53      ~r2_hidden(X0,k1_tarski(X1)) | k1_tarski(X0) = k1_tarski(X1) | sK3(X0,k1_tarski(X1)) = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u113,axiom,
% 0.22/0.53      ~r2_hidden(X4,k1_tarski(X3)) | sK3(X2,k1_tarski(X3)) = X4 | sK3(X2,k1_tarski(X3)) = X2 | k1_tarski(X3) = k1_tarski(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u116,axiom,
% 0.22/0.53      ~r2_hidden(X13,k1_tarski(X12)) | k1_tarski(X12) = k1_tarski(X13) | sK3(X11,k1_tarski(X12)) = sK3(X13,k1_tarski(X12)) | sK3(X11,k1_tarski(X12)) = X11 | k1_tarski(X12) = k1_tarski(X11)).
% 0.22/0.53  
% 0.22/0.53  cnf(u70,negated_conjecture,
% 0.22/0.53      k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u97,axiom,
% 0.22/0.53      sK3(sK3(X1,k1_tarski(X2)),k1_tarski(X2)) = X2 | k1_tarski(X2) = k1_tarski(sK3(X1,k1_tarski(X2))) | sK3(X1,k1_tarski(X2)) = X1 | k1_tarski(X1) = k1_tarski(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u114,axiom,
% 0.22/0.53      sK3(X7,k1_tarski(X6)) = X7 | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6)) | sK3(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.22/0.53  
% 0.22/0.53  cnf(u60,axiom,
% 0.22/0.53      sK3(X0,k1_tarski(X1)) = X0 | sK3(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u60,axiom,
% 0.22/0.53      sK3(X0,k1_tarski(X1)) = X0 | sK3(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u114,axiom,
% 0.22/0.53      sK3(X7,k1_tarski(X6)) = X7 | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6)) | sK3(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.22/0.53  
% 0.22/0.53  cnf(u114,axiom,
% 0.22/0.53      sK3(X7,k1_tarski(X6)) = X7 | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6)) | sK3(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.22/0.53  
% 0.22/0.53  cnf(u109,axiom,
% 0.22/0.53      k1_tarski(X5) = k1_tarski(sK3(X4,k1_tarski(X5))) | sK3(X4,k1_tarski(X5)) = X4 | k1_tarski(X5) = k1_tarski(X4)).
% 0.22/0.53  
% 0.22/0.53  cnf(u38,axiom,
% 0.22/0.53      k1_tarski(X0) = k2_tarski(X0,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u177,axiom,
% 0.22/0.53      sK3(X2,k1_tarski(X1)) != X0 | sK3(X2,k1_tarski(X1)) = X2 | sK3(X0,k1_tarski(X1)) = X0 | k1_tarski(X1) = k1_tarski(X2) | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u175,axiom,
% 0.22/0.53      sK3(X2,k1_tarski(X1)) != X0 | sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1)) | sK3(X2,k1_tarski(X1)) = X2 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X1) = k1_tarski(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u85,axiom,
% 0.22/0.53      X0 != X1 | sK3(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u91,axiom,
% 0.22/0.53      X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK3(X0,k1_tarski(X1)) = X0).
% 0.22/0.53  
% 0.22/0.53  cnf(u72,negated_conjecture,
% 0.22/0.53      sK1 != k2_yellow_0(sK0,k1_tarski(sK1)) | sK1 != k1_yellow_0(sK0,k1_tarski(sK1))).
% 0.22/0.53  
% 0.22/0.53  % (14888)# SZS output end Saturation.
% 0.22/0.53  % (14888)------------------------------
% 0.22/0.53  % (14888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14888)Termination reason: Satisfiable
% 0.22/0.53  
% 0.22/0.53  % (14888)Memory used [KB]: 1791
% 0.22/0.53  % (14888)Time elapsed: 0.101 s
% 0.22/0.53  % (14888)------------------------------
% 0.22/0.53  % (14888)------------------------------
% 0.22/0.53  % (14885)Refutation not found, incomplete strategy% (14885)------------------------------
% 0.22/0.53  % (14885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14885)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14885)Memory used [KB]: 1791
% 0.22/0.53  % (14885)Time elapsed: 0.112 s
% 0.22/0.53  % (14885)------------------------------
% 0.22/0.53  % (14885)------------------------------
% 0.22/0.53  % (14880)Success in time 0.163 s
%------------------------------------------------------------------------------
