%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:54 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   38 (  38 expanded)
%              Number of leaves         :   38 (  38 expanded)
%              Depth                    :    0
%              Number of atoms          :  121 ( 121 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u17,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u37,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK3) )).

cnf(u90,negated_conjecture,
    ( ~ r2_lattice3(sK0,X5,X3)
    | ~ m1_subset_1(X4,u1_struct_0(sK0))
    | ~ r2_hidden(X4,X5)
    | r1_orders_2(sK0,X4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0)) )).

cnf(u92,negated_conjecture,
    ( ~ r2_lattice3(sK1,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X2)
    | r1_orders_2(sK1,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) )).

cnf(u39,negated_conjecture,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK3) )).

cnf(u40,negated_conjecture,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u113,negated_conjecture,
    ( r1_orders_2(sK0,sK6(sK1,sK2,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK1,sK2,X0) )).

cnf(u114,negated_conjecture,
    ( r1_orders_2(sK0,sK6(sK0,sK2,X1),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_lattice3(sK0,sK2,X1) )).

cnf(u105,negated_conjecture,
    ( r1_orders_2(sK0,sK5(sK1,sK2,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK1,sK2,X0) )).

cnf(u106,negated_conjecture,
    ( r1_orders_2(sK0,sK5(sK0,sK2,X1),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,X1) )).

cnf(u33,axiom,
    ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u29,axiom,
    ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u32,axiom,
    ( r2_hidden(sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u28,axiom,
    ( r2_hidden(sK5(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u96,negated_conjecture,
    ( ~ r2_hidden(X1,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u95,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | ~ r2_hidden(X0,sK2)
    | r1_orders_2(sK0,X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u26,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_orders_2(X0) )).

cnf(u71,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u25,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u88,negated_conjecture,
    ( m1_subset_1(sK6(sK1,X0,X1),u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_lattice3(sK1,X0,X1) )).

cnf(u31,axiom,
    ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u86,negated_conjecture,
    ( m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_lattice3(sK1,X0,X1) )).

cnf(u27,axiom,
    ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u98,negated_conjecture,
    ( ~ m1_subset_1(sK6(X2,sK2,X3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK6(X2,sK2,X3),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | r2_lattice3(X2,sK2,X3) )).

cnf(u97,negated_conjecture,
    ( ~ m1_subset_1(sK5(X0,sK2,X1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK5(X0,sK2,X1),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,sK2,X1) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X0 = X2 )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X1 = X3 )).

cnf(u24,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u22,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u41,axiom,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = X1
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u62,axiom,
    ( ~ l1_orders_2(X0)
    | u1_orders_2(X0) = X2
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u30,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_lattice3(X0,X1,X2) )).

cnf(u68,negated_conjecture,
    ( u1_orders_2(sK0) = u1_orders_2(sK1) )).

cnf(u49,negated_conjecture,
    ( u1_struct_0(sK1) = u1_struct_0(sK0) )).

cnf(u20,negated_conjecture,
    ( sK3 = sK4 )).

cnf(u43,negated_conjecture,
    ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = X2 )).

cnf(u69,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = X1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:57:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (4929)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.48  % (4936)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (4944)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (4933)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (4952)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (4953)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (4930)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (4943)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (4953)Refutation not found, incomplete strategy% (4953)------------------------------
% 0.22/0.52  % (4953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4953)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4953)Memory used [KB]: 6268
% 0.22/0.52  % (4953)Time elapsed: 0.120 s
% 0.22/0.52  % (4953)------------------------------
% 0.22/0.52  % (4953)------------------------------
% 0.22/0.53  % (4942)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (4935)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (4949)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (4932)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (4949)Refutation not found, incomplete strategy% (4949)------------------------------
% 0.22/0.54  % (4949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4949)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4949)Memory used [KB]: 1791
% 0.22/0.54  % (4949)Time elapsed: 0.131 s
% 0.22/0.54  % (4949)------------------------------
% 0.22/0.54  % (4949)------------------------------
% 0.22/0.54  % (4950)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (4935)Refutation not found, incomplete strategy% (4935)------------------------------
% 0.22/0.54  % (4935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4932)Refutation not found, incomplete strategy% (4932)------------------------------
% 0.22/0.54  % (4932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4932)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4932)Memory used [KB]: 6268
% 0.22/0.54  % (4932)Time elapsed: 0.112 s
% 0.22/0.54  % (4932)------------------------------
% 0.22/0.54  % (4932)------------------------------
% 0.22/0.54  % (4935)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4935)Memory used [KB]: 6268
% 0.22/0.54  % (4935)Time elapsed: 0.075 s
% 0.22/0.54  % (4935)------------------------------
% 0.22/0.54  % (4935)------------------------------
% 0.22/0.54  % (4937)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (4934)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (4948)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (4939)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (4933)Refutation not found, incomplete strategy% (4933)------------------------------
% 0.22/0.54  % (4933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4933)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4933)Memory used [KB]: 6396
% 0.22/0.54  % (4933)Time elapsed: 0.131 s
% 0.22/0.54  % (4933)------------------------------
% 0.22/0.54  % (4933)------------------------------
% 0.22/0.54  % (4928)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (4930)Refutation not found, incomplete strategy% (4930)------------------------------
% 0.22/0.54  % (4930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4930)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4930)Memory used [KB]: 10746
% 0.22/0.54  % (4930)Time elapsed: 0.128 s
% 0.22/0.54  % (4930)------------------------------
% 0.22/0.54  % (4930)------------------------------
% 0.22/0.54  % (4955)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (4945)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (4941)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (4931)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (4945)Refutation not found, incomplete strategy% (4945)------------------------------
% 0.22/0.55  % (4945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4945)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4945)Memory used [KB]: 10746
% 0.22/0.55  % (4945)Time elapsed: 0.131 s
% 0.22/0.55  % (4945)------------------------------
% 0.22/0.55  % (4945)------------------------------
% 0.22/0.55  % (4931)Refutation not found, incomplete strategy% (4931)------------------------------
% 0.22/0.55  % (4931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4931)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4931)Memory used [KB]: 10746
% 0.22/0.55  % (4931)Time elapsed: 0.126 s
% 0.22/0.55  % (4931)------------------------------
% 0.22/0.55  % (4931)------------------------------
% 0.22/0.55  % (4956)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (4958)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (4946)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (4958)Refutation not found, incomplete strategy% (4958)------------------------------
% 0.22/0.56  % (4958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4958)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4958)Memory used [KB]: 1918
% 0.22/0.56  % (4958)Time elapsed: 0.138 s
% 0.22/0.56  % (4958)------------------------------
% 0.22/0.56  % (4958)------------------------------
% 0.22/0.56  % (4954)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (4957)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (4938)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.56  % (4934)# SZS output start Saturation.
% 0.22/0.56  cnf(u17,negated_conjecture,
% 0.22/0.56      r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.22/0.56  
% 0.22/0.56  cnf(u37,negated_conjecture,
% 0.22/0.56      r2_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK1,sK2,sK3)).
% 0.22/0.56  
% 0.22/0.56  cnf(u90,negated_conjecture,
% 0.22/0.56      ~r2_lattice3(sK0,X5,X3) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,X5) | r1_orders_2(sK0,X4,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))).
% 0.22/0.56  
% 0.22/0.56  cnf(u92,negated_conjecture,
% 0.22/0.56      ~r2_lattice3(sK1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r1_orders_2(sK1,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))).
% 0.22/0.56  
% 0.22/0.56  cnf(u39,negated_conjecture,
% 0.22/0.56      ~r2_lattice3(sK1,sK2,sK3) | ~r1_lattice3(sK1,sK2,sK3)).
% 0.22/0.56  
% 0.22/0.56  cnf(u40,negated_conjecture,
% 0.22/0.56      ~r2_lattice3(sK1,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.22/0.56  
% 0.22/0.56  cnf(u113,negated_conjecture,
% 0.22/0.56      r1_orders_2(sK0,sK6(sK1,sK2,X0),sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | r2_lattice3(sK1,sK2,X0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u114,negated_conjecture,
% 0.22/0.56      r1_orders_2(sK0,sK6(sK0,sK2,X1),sK3) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,sK2,X1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u105,negated_conjecture,
% 0.22/0.56      r1_orders_2(sK0,sK5(sK1,sK2,X0),sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK1,sK2,X0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u106,negated_conjecture,
% 0.22/0.56      r1_orders_2(sK0,sK5(sK0,sK2,X1),sK3) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,X1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u33,axiom,
% 0.22/0.56      ~r1_orders_2(X0,sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u29,axiom,
% 0.22/0.56      ~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u32,axiom,
% 0.22/0.56      r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u28,axiom,
% 0.22/0.56      r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u96,negated_conjecture,
% 0.22/0.56      ~r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.22/0.56  
% 0.22/0.56  cnf(u95,negated_conjecture,
% 0.22/0.56      ~r1_lattice3(sK1,sK2,sK3) | ~r2_hidden(X0,sK2) | r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.22/0.56  
% 0.22/0.56  cnf(u26,axiom,
% 0.22/0.56      ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~l1_orders_2(X0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u71,negated_conjecture,
% 0.22/0.56      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.56  
% 0.22/0.56  cnf(u25,axiom,
% 0.22/0.56      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u88,negated_conjecture,
% 0.22/0.56      m1_subset_1(sK6(sK1,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK1,X0,X1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u31,axiom,
% 0.22/0.56      m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u86,negated_conjecture,
% 0.22/0.56      m1_subset_1(sK5(sK1,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK1,X0,X1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u27,axiom,
% 0.22/0.56      m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u21,negated_conjecture,
% 0.22/0.56      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.22/0.56  
% 0.22/0.56  cnf(u98,negated_conjecture,
% 0.22/0.56      ~m1_subset_1(sK6(X2,sK2,X3),u1_struct_0(sK0)) | r1_orders_2(sK0,sK6(X2,sK2,X3),sK3) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2) | r2_lattice3(X2,sK2,X3)).
% 0.22/0.56  
% 0.22/0.56  cnf(u97,negated_conjecture,
% 0.22/0.56      ~m1_subset_1(sK5(X0,sK2,X1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK5(X0,sK2,X1),sK3) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,sK2,X1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u34,axiom,
% 0.22/0.56      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.22/0.56  
% 0.22/0.56  cnf(u35,axiom,
% 0.22/0.56      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.22/0.56  
% 0.22/0.56  cnf(u24,negated_conjecture,
% 0.22/0.56      l1_orders_2(sK0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u22,negated_conjecture,
% 0.22/0.56      l1_orders_2(sK1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u41,axiom,
% 0.22/0.56      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u62,axiom,
% 0.22/0.56      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u30,axiom,
% 0.22/0.56      ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u68,negated_conjecture,
% 0.22/0.56      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u49,negated_conjecture,
% 0.22/0.56      u1_struct_0(sK1) = u1_struct_0(sK0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u20,negated_conjecture,
% 0.22/0.56      sK3 = sK4).
% 0.22/0.56  
% 0.22/0.56  cnf(u43,negated_conjecture,
% 0.22/0.56      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.22/0.56  
% 0.22/0.56  cnf(u69,negated_conjecture,
% 0.22/0.56      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 0.22/0.56  
% 0.22/0.56  % (4934)# SZS output end Saturation.
% 0.22/0.56  % (4934)------------------------------
% 0.22/0.56  % (4934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4934)Termination reason: Satisfiable
% 0.22/0.56  
% 0.22/0.56  % (4934)Memory used [KB]: 6268
% 0.22/0.56  % (4934)Time elapsed: 0.145 s
% 0.22/0.56  % (4934)------------------------------
% 0.22/0.56  % (4934)------------------------------
% 0.22/0.56  % (4924)Success in time 0.193 s
%------------------------------------------------------------------------------
