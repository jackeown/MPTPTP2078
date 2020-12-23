%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:36 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   54 (  54 expanded)
%              Number of leaves         :   54 (  54 expanded)
%              Depth                    :    0
%              Number of atoms          :   69 (  69 expanded)
%              Number of equality atoms :   49 (  49 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u68,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u38,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u35,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u207,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) )).

% (4709)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
cnf(u215,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1) )).

cnf(u217,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4) )).

cnf(u216,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0) )).

cnf(u211,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k4_subset_1(X2,X1,k1_xboole_0) = X1 )).

cnf(u209,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k4_subset_1(X4,X3,X4) = k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) )).

cnf(u86,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u85,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u62,axiom,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) )).

cnf(u187,axiom,
    ( r1_tarski(k7_subset_1(X4,X4,k1_setfam_1(k2_tarski(X4,X5))),X4) )).

cnf(u70,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u71,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u43,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u69,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

cnf(u59,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u157,axiom,
    ( k1_setfam_1(k2_tarski(X3,k7_subset_1(X3,X3,X4))) = k7_subset_1(X3,X3,k1_setfam_1(k2_tarski(X3,X4))) )).

cnf(u136,axiom,
    ( k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k2_tarski(X2,X3)) )).

cnf(u89,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u144,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u84,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X2) )).

cnf(u33,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u82,axiom,
    ( k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) )).

cnf(u251,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u247,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u250,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u224,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

cnf(u222,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u260,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) )).

cnf(u213,axiom,
    ( k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u212,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u274,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) )).

cnf(u255,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u75,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u78,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u253,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u252,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) )).

cnf(u166,axiom,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k2_tarski(X0,X1)))) )).

cnf(u143,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,X1) )).

cnf(u161,axiom,
    ( k5_xboole_0(X3,k7_subset_1(k7_subset_1(X3,X3,X4),k7_subset_1(X3,X3,X4),X3)) = k5_xboole_0(k7_subset_1(X3,X3,X4),k1_setfam_1(k2_tarski(X3,X4))) )).

cnf(u90,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) )).

cnf(u61,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u98,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u235,axiom,
    ( k4_subset_1(X0,k1_xboole_0,X0) = X0 )).

cnf(u237,axiom,
    ( k4_subset_1(X1,X1,X1) = X1 )).

cnf(u214,axiom,
    ( k4_subset_1(X1,X1,k1_xboole_0) = X1 )).

cnf(u58,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u109,axiom,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u40,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u67,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (4694)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (4694)Refutation not found, incomplete strategy% (4694)------------------------------
% 0.20/0.50  % (4694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4710)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (4701)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (4684)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (4686)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (4683)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (4685)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (4681)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (4681)Refutation not found, incomplete strategy% (4681)------------------------------
% 0.20/0.51  % (4681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4681)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4681)Memory used [KB]: 1663
% 0.20/0.51  % (4681)Time elapsed: 0.107 s
% 0.20/0.51  % (4681)------------------------------
% 0.20/0.51  % (4681)------------------------------
% 0.20/0.51  % (4694)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4694)Memory used [KB]: 6268
% 0.20/0.51  % (4694)Time elapsed: 0.098 s
% 0.20/0.51  % (4694)------------------------------
% 0.20/0.51  % (4694)------------------------------
% 0.20/0.52  % (4704)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (4696)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (4700)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (4688)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (4704)Refutation not found, incomplete strategy% (4704)------------------------------
% 0.20/0.53  % (4704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4698)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (4682)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (4704)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4704)Memory used [KB]: 10746
% 0.20/0.53  % (4704)Time elapsed: 0.072 s
% 0.20/0.53  % (4704)------------------------------
% 0.20/0.53  % (4704)------------------------------
% 0.20/0.53  % (4693)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (4702)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (4697)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (4697)Refutation not found, incomplete strategy% (4697)------------------------------
% 0.20/0.53  % (4697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4697)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4697)Memory used [KB]: 6140
% 0.20/0.53  % (4697)Time elapsed: 0.001 s
% 0.20/0.53  % (4697)------------------------------
% 0.20/0.53  % (4697)------------------------------
% 0.20/0.53  % (4693)Refutation not found, incomplete strategy% (4693)------------------------------
% 0.20/0.53  % (4693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4693)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4693)Memory used [KB]: 10618
% 0.20/0.53  % (4693)Time elapsed: 0.132 s
% 0.20/0.53  % (4693)------------------------------
% 0.20/0.53  % (4693)------------------------------
% 0.20/0.53  % (4692)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (4707)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (4689)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (4684)Refutation not found, incomplete strategy% (4684)------------------------------
% 0.20/0.54  % (4684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4684)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (4684)Memory used [KB]: 10874
% 0.20/0.54  % (4684)Time elapsed: 0.139 s
% 0.20/0.54  % (4684)------------------------------
% 0.20/0.54  % (4684)------------------------------
% 0.20/0.54  % (4691)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.54  % (4688)# SZS output start Saturation.
% 0.20/0.54  cnf(u68,axiom,
% 0.20/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u38,axiom,
% 0.20/0.54      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u35,negated_conjecture,
% 0.20/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.54  
% 0.20/0.54  cnf(u207,negated_conjecture,
% 0.20/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))).
% 0.20/0.54  
% 0.20/0.54  % (4709)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  cnf(u215,negated_conjecture,
% 0.20/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u217,axiom,
% 0.20/0.54      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4)).
% 0.20/0.54  
% 0.20/0.54  cnf(u216,axiom,
% 0.20/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u211,axiom,
% 0.20/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k4_subset_1(X2,X1,k1_xboole_0) = X1).
% 0.20/0.54  
% 0.20/0.54  cnf(u209,axiom,
% 0.20/0.54      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k4_subset_1(X4,X3,X4) = k5_xboole_0(X3,k7_subset_1(X4,X4,X3))).
% 0.20/0.54  
% 0.20/0.54  cnf(u86,axiom,
% 0.20/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u85,axiom,
% 0.20/0.54      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1))).
% 0.20/0.54  
% 0.20/0.54  cnf(u52,axiom,
% 0.20/0.54      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u51,axiom,
% 0.20/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.20/0.54  
% 0.20/0.54  cnf(u62,axiom,
% 0.20/0.54      r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u187,axiom,
% 0.20/0.54      r1_tarski(k7_subset_1(X4,X4,k1_setfam_1(k2_tarski(X4,X5))),X4)).
% 0.20/0.54  
% 0.20/0.54  cnf(u70,axiom,
% 0.20/0.54      r1_tarski(k1_xboole_0,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u71,axiom,
% 0.20/0.54      r1_tarski(X1,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u43,axiom,
% 0.20/0.54      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u69,axiom,
% 0.20/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u59,axiom,
% 0.20/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u157,axiom,
% 0.20/0.54      k1_setfam_1(k2_tarski(X3,k7_subset_1(X3,X3,X4))) = k7_subset_1(X3,X3,k1_setfam_1(k2_tarski(X3,X4)))).
% 0.20/0.54  
% 0.20/0.54  cnf(u136,axiom,
% 0.20/0.54      k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k2_tarski(X2,X3))).
% 0.20/0.54  
% 0.20/0.54  cnf(u89,negated_conjecture,
% 0.20/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u144,axiom,
% 0.20/0.54      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u84,axiom,
% 0.20/0.54      k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u33,negated_conjecture,
% 0.20/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u82,axiom,
% 0.20/0.54      k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4)))).
% 0.20/0.54  
% 0.20/0.54  cnf(u251,negated_conjecture,
% 0.20/0.54      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u247,negated_conjecture,
% 0.20/0.54      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u250,negated_conjecture,
% 0.20/0.54      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u224,negated_conjecture,
% 0.20/0.54      sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u222,negated_conjecture,
% 0.20/0.54      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u260,negated_conjecture,
% 0.20/0.54      k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u213,axiom,
% 0.20/0.54      k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u212,negated_conjecture,
% 0.20/0.54      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u274,negated_conjecture,
% 0.20/0.54      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))).
% 0.20/0.54  
% 0.20/0.54  cnf(u255,negated_conjecture,
% 0.20/0.54      sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.20/0.54  
% 0.20/0.54  cnf(u75,negated_conjecture,
% 0.20/0.54      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.54  
% 0.20/0.54  cnf(u78,axiom,
% 0.20/0.54      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u253,negated_conjecture,
% 0.20/0.54      u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.20/0.54  
% 0.20/0.54  cnf(u252,negated_conjecture,
% 0.20/0.54      u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))).
% 0.20/0.54  
% 0.20/0.54  cnf(u166,axiom,
% 0.20/0.54      k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k2_tarski(X0,X1))))).
% 0.20/0.54  
% 0.20/0.54  cnf(u143,axiom,
% 0.20/0.54      k1_xboole_0 = k5_xboole_0(X1,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u161,axiom,
% 0.20/0.54      k5_xboole_0(X3,k7_subset_1(k7_subset_1(X3,X3,X4),k7_subset_1(X3,X3,X4),X3)) = k5_xboole_0(k7_subset_1(X3,X3,X4),k1_setfam_1(k2_tarski(X3,X4)))).
% 0.20/0.54  
% 0.20/0.54  cnf(u90,axiom,
% 0.20/0.54      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1))).
% 0.20/0.54  
% 0.20/0.54  cnf(u61,axiom,
% 0.20/0.54      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u98,axiom,
% 0.20/0.54      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u235,axiom,
% 0.20/0.54      k4_subset_1(X0,k1_xboole_0,X0) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u237,axiom,
% 0.20/0.54      k4_subset_1(X1,X1,X1) = X1).
% 0.20/0.54  
% 0.20/0.54  cnf(u214,axiom,
% 0.20/0.54      k4_subset_1(X1,X1,k1_xboole_0) = X1).
% 0.20/0.54  
% 0.20/0.54  cnf(u58,axiom,
% 0.20/0.54      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u109,axiom,
% 0.20/0.54      k5_xboole_0(k1_xboole_0,X0) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u40,axiom,
% 0.20/0.54      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u67,negated_conjecture,
% 0.20/0.54      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.20/0.54  
% 0.20/0.54  % (4688)# SZS output end Saturation.
% 0.20/0.54  % (4688)------------------------------
% 0.20/0.54  % (4688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (4688)Termination reason: Satisfiable
% 0.20/0.54  
% 0.20/0.54  % (4688)Memory used [KB]: 6396
% 0.20/0.54  % (4688)Time elapsed: 0.083 s
% 0.20/0.54  % (4688)------------------------------
% 0.20/0.54  % (4688)------------------------------
% 0.20/0.54  % (4703)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (4708)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (4677)Success in time 0.182 s
%------------------------------------------------------------------------------
