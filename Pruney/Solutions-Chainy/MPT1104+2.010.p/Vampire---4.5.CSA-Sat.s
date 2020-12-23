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
% DateTime   : Thu Dec  3 13:08:51 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   86 (  86 expanded)
%              Number of leaves         :   86 (  86 expanded)
%              Depth                    :    0
%              Number of atoms          :   95 (  95 expanded)
%              Number of equality atoms :   78 (  78 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u55,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u33,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u222,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2)) )).

cnf(u223,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1)) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u135,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u53,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )).

cnf(u224,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3) )).

cnf(u66,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u65,negated_conjecture,
    ( r1_tarski(sK2,u1_struct_0(sK0)) )).

cnf(u67,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u44,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u31,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u45,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u353,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u173,negated_conjecture,
    ( sK2 = k7_subset_1(sK2,sK2,sK1) )).

cnf(u253,negated_conjecture,
    ( sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2) )).

cnf(u350,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK1,k2_struct_0(sK0))) )).

cnf(u69,negated_conjecture,
    ( sK2 = k3_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u258,negated_conjecture,
    ( sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

cnf(u154,negated_conjecture,
    ( sK1 = k7_subset_1(sK1,sK1,sK2) )).

cnf(u269,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u259,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK2,k2_struct_0(sK0))) )).

cnf(u70,negated_conjecture,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u257,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))) )).

cnf(u356,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) )).

cnf(u261,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

cnf(u260,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(sK2,sK1) )).

cnf(u255,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(sK1,sK2) )).

cnf(u268,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u30,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u288,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u287,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u271,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u263,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) )).

cnf(u218,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u216,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u217,negated_conjecture,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

cnf(u215,negated_conjecture,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u198,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),k3_xboole_0(X1,k3_tarski(k2_tarski(X1,X0)))) )).

cnf(u151,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u290,axiom,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(k3_tarski(k2_tarski(X1,X0)),k3_tarski(k2_tarski(X1,X0)),X1) )).

cnf(u204,axiom,
    ( k7_subset_1(X2,X2,X3) = k7_subset_1(k3_tarski(k2_tarski(X2,X3)),k3_tarski(k2_tarski(X2,X3)),X3) )).

cnf(u139,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u138,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u289,axiom,
    ( k4_subset_1(X0,X0,X0) = X0 )).

cnf(u34,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u87,axiom,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 )).

cnf(u572,axiom,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X10,X9)),k3_tarski(k2_tarski(X10,X9)))) = k3_tarski(k2_tarski(X9,X10)) )).

cnf(u435,axiom,
    ( k3_tarski(k2_tarski(X2,X3)) = k3_tarski(k2_tarski(X3,X2)) )).

cnf(u543,axiom,
    ( k3_tarski(k2_tarski(X7,X6)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X7,X6)),k3_tarski(k2_tarski(X6,X7)))) )).

cnf(u322,axiom,
    ( k3_tarski(k2_tarski(X2,X3)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X3,X2)),k3_tarski(k2_tarski(X2,X3)))) )).

cnf(u369,axiom,
    ( k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )).

cnf(u308,axiom,
    ( k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0)))) )).

cnf(u307,axiom,
    ( k3_tarski(k2_tarski(X2,X1)) = k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X2)))) )).

cnf(u214,axiom,
    ( k3_tarski(k2_tarski(X5,X5)) = X5 )).

cnf(u82,axiom,
    ( k3_tarski(k2_tarski(X6,k1_xboole_0)) = X6 )).

cnf(u629,axiom,
    ( k3_tarski(k2_tarski(X1,X2)) = k5_xboole_0(k3_tarski(k2_tarski(X2,X1)),k1_xboole_0) )).

cnf(u137,axiom,
    ( k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) )).

cnf(u38,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u168,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK2) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) )).

cnf(u167,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u136,axiom,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(X1,k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X0,X0,X1) )).

cnf(u141,axiom,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k7_subset_1(X1,X1,X2) )).

cnf(u134,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) )).

cnf(u89,axiom,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u54,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u913,axiom,
    ( k1_xboole_0 = k5_xboole_0(k3_tarski(k2_tarski(X7,X6)),k3_xboole_0(k3_tarski(k2_tarski(X7,X6)),k3_tarski(k2_tarski(X6,X7)))) )).

cnf(u403,axiom,
    ( k1_xboole_0 = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),k3_xboole_0(k3_tarski(k2_tarski(X3,X2)),k3_tarski(k2_tarski(X2,X3)))) )).

cnf(u207,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,X1) )).

cnf(u256,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

cnf(u212,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK2,sK2,u1_struct_0(sK0)) )).

cnf(u363,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u210,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u404,axiom,
    ( k1_xboole_0 = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) )).

cnf(u153,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X6) )).

cnf(u390,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) )).

cnf(u387,axiom,
    ( k1_xboole_0 = k7_subset_1(X5,X5,k3_tarski(k2_tarski(X5,X6))) )).

cnf(u208,axiom,
    ( k1_xboole_0 = k7_subset_1(X5,X5,X5) )).

cnf(u71,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2) )).

cnf(u57,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u35,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u68,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u39,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u32,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:28:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (31054)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.48  % (31052)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.48  % (31072)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.48  % (31054)Refutation not found, incomplete strategy% (31054)------------------------------
% 0.21/0.48  % (31054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31052)Refutation not found, incomplete strategy% (31052)------------------------------
% 0.21/0.49  % (31052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31060)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (31052)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31052)Memory used [KB]: 1663
% 0.21/0.49  % (31052)Time elapsed: 0.077 s
% 0.21/0.49  % (31052)------------------------------
% 0.21/0.49  % (31052)------------------------------
% 0.21/0.49  % (31063)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (31054)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31054)Memory used [KB]: 10746
% 0.21/0.49  % (31054)Time elapsed: 0.076 s
% 0.21/0.49  % (31054)------------------------------
% 0.21/0.49  % (31054)------------------------------
% 0.21/0.49  % (31059)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (31056)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (31060)Refutation not found, incomplete strategy% (31060)------------------------------
% 0.21/0.50  % (31060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31060)Memory used [KB]: 10746
% 0.21/0.50  % (31060)Time elapsed: 0.093 s
% 0.21/0.50  % (31060)------------------------------
% 0.21/0.50  % (31060)------------------------------
% 0.21/0.50  % (31056)Refutation not found, incomplete strategy% (31056)------------------------------
% 0.21/0.50  % (31056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31056)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31057)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (31056)Memory used [KB]: 6268
% 0.21/0.50  % (31056)Time elapsed: 0.086 s
% 0.21/0.50  % (31056)------------------------------
% 0.21/0.50  % (31056)------------------------------
% 0.21/0.50  % (31081)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (31055)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (31071)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (31073)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (31073)Refutation not found, incomplete strategy% (31073)------------------------------
% 0.21/0.50  % (31073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31073)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31073)Memory used [KB]: 1663
% 0.21/0.50  % (31073)Time elapsed: 0.091 s
% 0.21/0.50  % (31073)------------------------------
% 0.21/0.50  % (31073)------------------------------
% 0.21/0.50  % (31062)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (31079)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (31066)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (31080)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (31058)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31076)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (31065)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (31061)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (31064)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31077)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (31063)Refutation not found, incomplete strategy% (31063)------------------------------
% 0.21/0.51  % (31063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31063)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31063)Memory used [KB]: 10746
% 0.21/0.51  % (31063)Time elapsed: 0.107 s
% 0.21/0.51  % (31063)------------------------------
% 0.21/0.51  % (31063)------------------------------
% 0.21/0.51  % (31075)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (31077)Refutation not found, incomplete strategy% (31077)------------------------------
% 0.21/0.52  % (31077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31077)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31077)Memory used [KB]: 6396
% 0.21/0.52  % (31077)Time elapsed: 0.109 s
% 0.21/0.52  % (31077)------------------------------
% 0.21/0.52  % (31077)------------------------------
% 0.21/0.52  % (31078)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (31074)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (31067)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (31067)Refutation not found, incomplete strategy% (31067)------------------------------
% 0.21/0.52  % (31067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31067)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31067)Memory used [KB]: 6140
% 0.21/0.52  % (31067)Time elapsed: 0.003 s
% 0.21/0.52  % (31067)------------------------------
% 0.21/0.52  % (31067)------------------------------
% 0.21/0.52  % (31062)Refutation not found, incomplete strategy% (31062)------------------------------
% 0.21/0.52  % (31062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31062)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31062)Memory used [KB]: 10618
% 0.21/0.52  % (31062)Time elapsed: 0.095 s
% 0.21/0.52  % (31062)------------------------------
% 0.21/0.52  % (31062)------------------------------
% 0.21/0.52  % (31074)Refutation not found, incomplete strategy% (31074)------------------------------
% 0.21/0.52  % (31074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31070)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (31078)Refutation not found, incomplete strategy% (31078)------------------------------
% 0.21/0.52  % (31078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31069)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (31068)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (31074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31074)Memory used [KB]: 10746
% 0.21/0.52  % (31074)Time elapsed: 0.119 s
% 0.21/0.52  % (31074)------------------------------
% 0.21/0.52  % (31074)------------------------------
% 0.21/0.53  % (31061)Refutation not found, incomplete strategy% (31061)------------------------------
% 0.21/0.53  % (31061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31069)Refutation not found, incomplete strategy% (31069)------------------------------
% 0.21/0.53  % (31069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31069)Memory used [KB]: 10618
% 0.21/0.53  % (31069)Time elapsed: 0.124 s
% 0.21/0.53  % (31069)------------------------------
% 0.21/0.53  % (31069)------------------------------
% 0.21/0.53  % (31061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31061)Memory used [KB]: 10746
% 0.21/0.53  % (31061)Time elapsed: 0.111 s
% 0.21/0.53  % (31061)------------------------------
% 0.21/0.53  % (31061)------------------------------
% 0.21/0.53  % (31053)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (31059)Refutation not found, incomplete strategy% (31059)------------------------------
% 0.21/0.53  % (31059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31078)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31078)Memory used [KB]: 10746
% 0.21/0.53  % (31078)Time elapsed: 0.119 s
% 0.21/0.53  % (31078)------------------------------
% 0.21/0.53  % (31078)------------------------------
% 0.21/0.55  % (31059)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31059)Memory used [KB]: 6524
% 0.21/0.55  % (31059)Time elapsed: 0.106 s
% 0.21/0.55  % (31059)------------------------------
% 0.21/0.55  % (31059)------------------------------
% 0.21/0.56  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.56  % (31058)# SZS output start Saturation.
% 0.21/0.56  cnf(u55,axiom,
% 0.21/0.56      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u33,negated_conjecture,
% 0.21/0.56      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u29,negated_conjecture,
% 0.21/0.56      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u222,negated_conjecture,
% 0.21/0.56      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))).
% 0.21/0.56  
% 0.21/0.56  cnf(u223,negated_conjecture,
% 0.21/0.56      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1))).
% 0.21/0.56  
% 0.21/0.56  cnf(u46,axiom,
% 0.21/0.56      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u135,axiom,
% 0.21/0.56      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u53,axiom,
% 0.21/0.56      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))).
% 0.21/0.56  
% 0.21/0.56  cnf(u224,axiom,
% 0.21/0.56      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3)).
% 0.21/0.56  
% 0.21/0.56  cnf(u66,negated_conjecture,
% 0.21/0.56      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u65,negated_conjecture,
% 0.21/0.56      r1_tarski(sK2,u1_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u67,axiom,
% 0.21/0.56      r1_tarski(X0,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u44,axiom,
% 0.21/0.56      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u31,negated_conjecture,
% 0.21/0.56      r1_xboole_0(sK1,sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u45,axiom,
% 0.21/0.56      ~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0).
% 0.21/0.56  
% 0.21/0.56  cnf(u353,negated_conjecture,
% 0.21/0.56      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u173,negated_conjecture,
% 0.21/0.56      sK2 = k7_subset_1(sK2,sK2,sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u253,negated_conjecture,
% 0.21/0.56      sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u350,negated_conjecture,
% 0.21/0.56      sK2 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK1,k2_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u69,negated_conjecture,
% 0.21/0.56      sK2 = k3_xboole_0(sK2,u1_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u258,negated_conjecture,
% 0.21/0.56      sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u154,negated_conjecture,
% 0.21/0.56      sK1 = k7_subset_1(sK1,sK1,sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u269,negated_conjecture,
% 0.21/0.56      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u259,negated_conjecture,
% 0.21/0.56      sK1 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK2,k2_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u70,negated_conjecture,
% 0.21/0.56      sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u257,negated_conjecture,
% 0.21/0.56      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK2,k2_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u356,negated_conjecture,
% 0.21/0.56      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k2_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u261,negated_conjecture,
% 0.21/0.56      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))).
% 0.21/0.56  
% 0.21/0.56  cnf(u260,negated_conjecture,
% 0.21/0.56      k2_struct_0(sK0) = k5_xboole_0(sK2,sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u255,negated_conjecture,
% 0.21/0.56      k2_struct_0(sK0) = k5_xboole_0(sK1,sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u268,negated_conjecture,
% 0.21/0.56      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u30,negated_conjecture,
% 0.21/0.56      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u288,negated_conjecture,
% 0.21/0.56      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u287,negated_conjecture,
% 0.21/0.56      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u271,negated_conjecture,
% 0.21/0.56      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u263,negated_conjecture,
% 0.21/0.56      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u218,negated_conjecture,
% 0.21/0.56      u1_struct_0(sK0) = k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))).
% 0.21/0.56  
% 0.21/0.56  cnf(u216,negated_conjecture,
% 0.21/0.56      u1_struct_0(sK0) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))).
% 0.21/0.56  
% 0.21/0.56  cnf(u217,negated_conjecture,
% 0.21/0.56      u1_struct_0(sK0) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u215,negated_conjecture,
% 0.21/0.56      u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u198,axiom,
% 0.21/0.56      k7_subset_1(X0,X0,X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),k3_xboole_0(X1,k3_tarski(k2_tarski(X1,X0))))).
% 0.21/0.56  
% 0.21/0.56  cnf(u151,axiom,
% 0.21/0.56      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u290,axiom,
% 0.21/0.56      k7_subset_1(X0,X0,X1) = k7_subset_1(k3_tarski(k2_tarski(X1,X0)),k3_tarski(k2_tarski(X1,X0)),X1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u204,axiom,
% 0.21/0.56      k7_subset_1(X2,X2,X3) = k7_subset_1(k3_tarski(k2_tarski(X2,X3)),k3_tarski(k2_tarski(X2,X3)),X3)).
% 0.21/0.56  
% 0.21/0.56  cnf(u139,negated_conjecture,
% 0.21/0.56      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u138,negated_conjecture,
% 0.21/0.56      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u289,axiom,
% 0.21/0.56      k4_subset_1(X0,X0,X0) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u34,axiom,
% 0.21/0.56      k2_subset_1(X0) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u87,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u572,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(k3_tarski(k2_tarski(X10,X9)),k3_tarski(k2_tarski(X10,X9)))) = k3_tarski(k2_tarski(X9,X10))).
% 0.21/0.56  
% 0.21/0.56  cnf(u435,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X2,X3)) = k3_tarski(k2_tarski(X3,X2))).
% 0.21/0.56  
% 0.21/0.56  cnf(u543,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X7,X6)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X7,X6)),k3_tarski(k2_tarski(X6,X7))))).
% 0.21/0.56  
% 0.21/0.56  cnf(u322,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X2,X3)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X3,X2)),k3_tarski(k2_tarski(X2,X3))))).
% 0.21/0.56  
% 0.21/0.56  cnf(u369,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))).
% 0.21/0.56  
% 0.21/0.56  cnf(u308,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X1,X0)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0))))).
% 0.21/0.56  
% 0.21/0.56  cnf(u307,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X2,X1)) = k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X2))))).
% 0.21/0.56  
% 0.21/0.56  cnf(u214,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X5,X5)) = X5).
% 0.21/0.56  
% 0.21/0.56  cnf(u82,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X6,k1_xboole_0)) = X6).
% 0.21/0.56  
% 0.21/0.56  cnf(u629,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X1,X2)) = k5_xboole_0(k3_tarski(k2_tarski(X2,X1)),k1_xboole_0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u137,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u38,axiom,
% 0.21/0.56      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u168,negated_conjecture,
% 0.21/0.56      k5_xboole_0(u1_struct_0(sK0),sK2) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u167,negated_conjecture,
% 0.21/0.56      k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u136,axiom,
% 0.21/0.56      k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(X1,k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X0,X0,X1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u141,axiom,
% 0.21/0.56      k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k7_subset_1(X1,X1,X2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u134,axiom,
% 0.21/0.56      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))).
% 0.21/0.56  
% 0.21/0.56  cnf(u89,axiom,
% 0.21/0.56      k5_xboole_0(k1_xboole_0,X0) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u54,axiom,
% 0.21/0.56      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u913,axiom,
% 0.21/0.56      k1_xboole_0 = k5_xboole_0(k3_tarski(k2_tarski(X7,X6)),k3_xboole_0(k3_tarski(k2_tarski(X7,X6)),k3_tarski(k2_tarski(X6,X7))))).
% 0.21/0.56  
% 0.21/0.56  cnf(u403,axiom,
% 0.21/0.56      k1_xboole_0 = k5_xboole_0(k3_tarski(k2_tarski(X2,X3)),k3_xboole_0(k3_tarski(k2_tarski(X3,X2)),k3_tarski(k2_tarski(X2,X3))))).
% 0.21/0.56  
% 0.21/0.56  cnf(u207,axiom,
% 0.21/0.56      k1_xboole_0 = k5_xboole_0(X1,X1)).
% 0.21/0.56  
% 0.21/0.56  cnf(u256,negated_conjecture,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u212,negated_conjecture,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(sK2,sK2,u1_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u363,negated_conjecture,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u210,negated_conjecture,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u404,axiom,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u153,axiom,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X6)).
% 0.21/0.56  
% 0.21/0.56  cnf(u390,axiom,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u387,axiom,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(X5,X5,k3_tarski(k2_tarski(X5,X6)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u208,axiom,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(X5,X5,X5)).
% 0.21/0.56  
% 0.21/0.56  cnf(u71,negated_conjecture,
% 0.21/0.56      k1_xboole_0 = k3_xboole_0(sK1,sK2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u57,axiom,
% 0.21/0.56      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u35,axiom,
% 0.21/0.56      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u68,axiom,
% 0.21/0.56      k3_xboole_0(X0,X0) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u39,axiom,
% 0.21/0.56      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u32,negated_conjecture,
% 0.21/0.56      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.56  
% 0.21/0.56  % (31058)# SZS output end Saturation.
% 0.21/0.56  % (31058)------------------------------
% 0.21/0.56  % (31058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (31058)Termination reason: Satisfiable
% 0.21/0.56  
% 0.21/0.56  % (31058)Memory used [KB]: 6652
% 0.21/0.56  % (31058)Time elapsed: 0.117 s
% 0.21/0.56  % (31058)------------------------------
% 0.21/0.56  % (31058)------------------------------
% 0.21/0.56  % (31051)Success in time 0.189 s
%------------------------------------------------------------------------------
