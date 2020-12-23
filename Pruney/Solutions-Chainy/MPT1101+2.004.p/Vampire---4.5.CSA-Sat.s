%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:28 EST 2020

% Result     : CounterSatisfiable 1.39s
% Output     : Saturation 1.39s
% Verified   : 
% Statistics : Number of clauses        :   51 (  51 expanded)
%              Number of leaves         :   51 (  51 expanded)
%              Depth                    :    0
%              Number of atoms          :   68 (  68 expanded)
%              Number of equality atoms :   40 (  40 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u65,axiom,
    ( m1_subset_1(k3_subset_1(X4,X4),k1_zfmisc_1(X4)) )).

cnf(u40,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u43,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u49,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1) )).

cnf(u50,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u99,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 )).

cnf(u76,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,k3_subset_1(X0,X0)) = k2_xboole_0(X1,k3_subset_1(X0,X0)) )).

cnf(u62,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X0) = k2_xboole_0(X1,X0) )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u28,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) )).

cnf(u80,axiom,
    ( r1_tarski(k3_subset_1(X5,X5),X5) )).

cnf(u54,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u39,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u37,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u68,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u45,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) )).

cnf(u93,axiom,
    ( ~ r1_tarski(X0,k3_subset_1(X0,X0))
    | k3_subset_1(X0,X0) = X0 )).

cnf(u35,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u27,axiom,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 )).

cnf(u33,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u118,axiom,
    ( k3_subset_1(X1,X1) = k4_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1)) )).

cnf(u105,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u75,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u90,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u89,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u104,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u60,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u44,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u113,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u114,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u81,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u82,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) )).

cnf(u73,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u67,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u101,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u102,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u69,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u46,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u96,axiom,
    ( k2_subset_1(X1) = X1 )).

cnf(u97,axiom,
    ( k4_subset_1(X2,k3_subset_1(X2,X2),X2) = X2 )).

cnf(u91,axiom,
    ( k4_subset_1(X0,X0,X0) = X0 )).

cnf(u98,axiom,
    ( k4_subset_1(X2,X2,k3_subset_1(X2,X2)) = X2 )).

cnf(u100,axiom,
    ( k3_subset_1(X0,k1_subset_1(X0)) = X0 )).

cnf(u64,axiom,
    ( k3_subset_1(X3,k3_subset_1(X3,X3)) = X3 )).

cnf(u117,axiom,
    ( k2_xboole_0(X0,k3_subset_1(X0,X0)) = X0 )).

cnf(u94,axiom,
    ( k2_xboole_0(k3_subset_1(X1,X1),X1) = X1 )).

cnf(u41,axiom,
    ( k2_xboole_0(X0,X0) = X0 )).

cnf(u103,negated_conjecture,
    ( u1_struct_0(sK0) != k2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:59:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (31512)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.49  % (31505)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.49  % (31520)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.50  % (31520)Refutation not found, incomplete strategy% (31520)------------------------------
% 0.21/0.50  % (31520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31505)Refutation not found, incomplete strategy% (31505)------------------------------
% 0.21/0.50  % (31505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31508)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (31520)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31520)Memory used [KB]: 6268
% 0.21/0.50  % (31520)Time elapsed: 0.095 s
% 0.21/0.50  % (31520)------------------------------
% 0.21/0.50  % (31520)------------------------------
% 0.21/0.50  % (31505)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31505)Memory used [KB]: 10746
% 0.21/0.50  % (31505)Time elapsed: 0.097 s
% 0.21/0.50  % (31505)------------------------------
% 0.21/0.50  % (31505)------------------------------
% 0.21/0.51  % (31501)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31498)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (31500)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (31497)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.52  % (31515)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.53  % (31496)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.53  % (31514)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.23/0.53  % (31517)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.23/0.53  % (31518)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.23/0.53  % (31523)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.23/0.53  % (31509)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.53  % (31495)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.23/0.54  % (31516)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.23/0.54  % (31523)Refutation not found, incomplete strategy% (31523)------------------------------
% 1.23/0.54  % (31523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (31523)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (31523)Memory used [KB]: 10746
% 1.23/0.54  % (31523)Time elapsed: 0.128 s
% 1.23/0.54  % (31523)------------------------------
% 1.23/0.54  % (31523)------------------------------
% 1.23/0.54  % (31507)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.54  % (31507)Refutation not found, incomplete strategy% (31507)------------------------------
% 1.23/0.54  % (31507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (31507)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (31507)Memory used [KB]: 10618
% 1.23/0.54  % (31507)Time elapsed: 0.126 s
% 1.23/0.54  % (31507)------------------------------
% 1.23/0.54  % (31507)------------------------------
% 1.23/0.54  % (31499)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.39/0.54  % (31504)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.54  % (31510)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.54  % (31524)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.54  % (31496)Refutation not found, incomplete strategy% (31496)------------------------------
% 1.39/0.54  % (31496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (31496)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (31496)Memory used [KB]: 1663
% 1.39/0.54  % (31496)Time elapsed: 0.106 s
% 1.39/0.54  % (31496)------------------------------
% 1.39/0.54  % (31496)------------------------------
% 1.39/0.54  % (31524)Refutation not found, incomplete strategy% (31524)------------------------------
% 1.39/0.54  % (31524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (31524)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (31524)Memory used [KB]: 1663
% 1.39/0.54  % (31524)Time elapsed: 0.002 s
% 1.39/0.54  % (31524)------------------------------
% 1.39/0.54  % (31524)------------------------------
% 1.39/0.55  % (31506)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.55  % (31519)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.55  % (31521)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (31504)Refutation not found, incomplete strategy% (31504)------------------------------
% 1.39/0.55  % (31504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (31504)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (31504)Memory used [KB]: 1791
% 1.39/0.55  % (31504)Time elapsed: 0.140 s
% 1.39/0.55  % (31504)------------------------------
% 1.39/0.55  % (31504)------------------------------
% 1.39/0.55  % (31503)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.55  % (31511)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.55  % (31511)Refutation not found, incomplete strategy% (31511)------------------------------
% 1.39/0.55  % (31511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (31521)Refutation not found, incomplete strategy% (31521)------------------------------
% 1.39/0.56  % (31521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (31521)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (31521)Memory used [KB]: 6268
% 1.39/0.56  % (31521)Time elapsed: 0.153 s
% 1.39/0.56  % (31521)------------------------------
% 1.39/0.56  % (31521)------------------------------
% 1.39/0.56  % (31522)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.39/0.56  % (31502)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.57  % (31511)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (31511)Memory used [KB]: 10618
% 1.39/0.57  % (31511)Time elapsed: 0.152 s
% 1.39/0.57  % (31511)------------------------------
% 1.39/0.57  % (31511)------------------------------
% 1.39/0.58  % (31513)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.60  % SZS status CounterSatisfiable for theBenchmark
% 1.39/0.60  % (31502)# SZS output start Saturation.
% 1.39/0.60  cnf(u65,axiom,
% 1.39/0.60      m1_subset_1(k3_subset_1(X4,X4),k1_zfmisc_1(X4))).
% 1.39/0.60  
% 1.39/0.60  cnf(u40,axiom,
% 1.39/0.60      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.39/0.60  
% 1.39/0.60  cnf(u43,negated_conjecture,
% 1.39/0.60      m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.39/0.60  
% 1.39/0.60  cnf(u24,negated_conjecture,
% 1.39/0.60      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.39/0.60  
% 1.39/0.60  cnf(u49,negated_conjecture,
% 1.39/0.60      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1)).
% 1.39/0.60  
% 1.39/0.60  cnf(u50,negated_conjecture,
% 1.39/0.60      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.39/0.60  
% 1.39/0.60  cnf(u99,axiom,
% 1.39/0.60      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0).
% 1.39/0.60  
% 1.39/0.60  cnf(u76,axiom,
% 1.39/0.60      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X0)) = k2_xboole_0(X1,k3_subset_1(X0,X0))).
% 1.39/0.60  
% 1.39/0.60  cnf(u62,axiom,
% 1.39/0.60      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X0) = k2_xboole_0(X1,X0)).
% 1.39/0.60  
% 1.39/0.60  cnf(u36,axiom,
% 1.39/0.60      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 1.39/0.60  
% 1.39/0.60  cnf(u34,axiom,
% 1.39/0.60      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 1.39/0.60  
% 1.39/0.60  cnf(u29,axiom,
% 1.39/0.60      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 1.39/0.60  
% 1.39/0.60  cnf(u28,axiom,
% 1.39/0.60      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))).
% 1.39/0.60  
% 1.39/0.60  cnf(u80,axiom,
% 1.39/0.60      r1_tarski(k3_subset_1(X5,X5),X5)).
% 1.39/0.60  
% 1.39/0.60  cnf(u54,negated_conjecture,
% 1.39/0.60      r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 1.39/0.60  
% 1.39/0.60  cnf(u39,negated_conjecture,
% 1.39/0.60      r1_tarski(sK1,u1_struct_0(sK0))).
% 1.39/0.60  
% 1.39/0.60  cnf(u37,axiom,
% 1.39/0.60      r1_tarski(X1,X1)).
% 1.39/0.60  
% 1.39/0.60  cnf(u68,negated_conjecture,
% 1.39/0.60      ~r1_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1)).
% 1.39/0.60  
% 1.39/0.60  cnf(u45,negated_conjecture,
% 1.39/0.60      ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)).
% 1.39/0.60  
% 1.39/0.60  cnf(u93,axiom,
% 1.39/0.60      ~r1_tarski(X0,k3_subset_1(X0,X0)) | k3_subset_1(X0,X0) = X0).
% 1.39/0.60  
% 1.39/0.60  cnf(u35,axiom,
% 1.39/0.60      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 1.39/0.60  
% 1.39/0.60  cnf(u27,axiom,
% 1.39/0.60      ~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1).
% 1.39/0.60  
% 1.39/0.60  cnf(u33,axiom,
% 1.39/0.60      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 1.39/0.60  
% 1.39/0.60  cnf(u118,axiom,
% 1.39/0.60      k3_subset_1(X1,X1) = k4_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1))).
% 1.39/0.60  
% 1.39/0.60  cnf(u105,negated_conjecture,
% 1.39/0.60      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.39/0.60  
% 1.39/0.60  cnf(u75,negated_conjecture,
% 1.39/0.60      k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.39/0.60  
% 1.39/0.60  cnf(u90,negated_conjecture,
% 1.39/0.60      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 1.39/0.60  
% 1.39/0.60  cnf(u89,negated_conjecture,
% 1.39/0.60      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.39/0.60  
% 1.39/0.60  cnf(u104,negated_conjecture,
% 1.39/0.60      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 1.39/0.60  
% 1.39/0.60  cnf(u60,negated_conjecture,
% 1.39/0.60      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.39/0.60  
% 1.39/0.60  cnf(u44,negated_conjecture,
% 1.39/0.60      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.39/0.60  
% 1.39/0.60  cnf(u113,negated_conjecture,
% 1.39/0.60      k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 1.39/0.60  
% 1.39/0.60  cnf(u114,negated_conjecture,
% 1.39/0.60      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 1.39/0.60  
% 1.39/0.60  cnf(u81,negated_conjecture,
% 1.39/0.60      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.39/0.60  
% 1.39/0.60  cnf(u82,negated_conjecture,
% 1.39/0.60      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK1)).
% 1.39/0.60  
% 1.39/0.60  cnf(u73,negated_conjecture,
% 1.39/0.60      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.39/0.60  
% 1.39/0.60  cnf(u67,negated_conjecture,
% 1.39/0.60      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1)).
% 1.39/0.60  
% 1.39/0.60  cnf(u101,negated_conjecture,
% 1.39/0.60      u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.39/0.60  
% 1.39/0.60  cnf(u102,negated_conjecture,
% 1.39/0.60      u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 1.39/0.60  
% 1.39/0.60  cnf(u69,negated_conjecture,
% 1.39/0.60      u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 1.39/0.60  
% 1.39/0.60  cnf(u46,negated_conjecture,
% 1.39/0.60      u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 1.39/0.60  
% 1.39/0.60  cnf(u96,axiom,
% 1.39/0.60      k2_subset_1(X1) = X1).
% 1.39/0.60  
% 1.39/0.60  cnf(u97,axiom,
% 1.39/0.60      k4_subset_1(X2,k3_subset_1(X2,X2),X2) = X2).
% 1.39/0.60  
% 1.39/0.60  cnf(u91,axiom,
% 1.39/0.60      k4_subset_1(X0,X0,X0) = X0).
% 1.39/0.60  
% 1.39/0.60  cnf(u98,axiom,
% 1.39/0.60      k4_subset_1(X2,X2,k3_subset_1(X2,X2)) = X2).
% 1.39/0.60  
% 1.39/0.60  cnf(u100,axiom,
% 1.39/0.60      k3_subset_1(X0,k1_subset_1(X0)) = X0).
% 1.39/0.60  
% 1.39/0.60  cnf(u64,axiom,
% 1.39/0.60      k3_subset_1(X3,k3_subset_1(X3,X3)) = X3).
% 1.39/0.60  
% 1.39/0.60  cnf(u117,axiom,
% 1.39/0.60      k2_xboole_0(X0,k3_subset_1(X0,X0)) = X0).
% 1.39/0.60  
% 1.39/0.60  cnf(u94,axiom,
% 1.39/0.60      k2_xboole_0(k3_subset_1(X1,X1),X1) = X1).
% 1.39/0.60  
% 1.39/0.60  cnf(u41,axiom,
% 1.39/0.60      k2_xboole_0(X0,X0) = X0).
% 1.39/0.60  
% 1.39/0.60  cnf(u103,negated_conjecture,
% 1.39/0.60      u1_struct_0(sK0) != k2_struct_0(sK0)).
% 1.39/0.60  
% 1.39/0.60  % (31502)# SZS output end Saturation.
% 1.39/0.60  % (31502)------------------------------
% 1.39/0.60  % (31502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.60  % (31502)Termination reason: Satisfiable
% 1.39/0.60  
% 1.39/0.60  % (31502)Memory used [KB]: 1791
% 1.39/0.60  % (31502)Time elapsed: 0.194 s
% 1.39/0.60  % (31502)------------------------------
% 1.39/0.60  % (31502)------------------------------
% 1.39/0.60  % (31491)Success in time 0.234 s
%------------------------------------------------------------------------------
