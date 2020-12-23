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
% DateTime   : Thu Dec  3 13:08:44 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   49 (  49 expanded)
%              Number of leaves         :   49 (  49 expanded)
%              Depth                    :    0
%              Number of atoms          :   64 (  64 expanded)
%              Number of equality atoms :   47 (  47 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u72,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u41,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u37,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u79,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1) )).

cnf(u86,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1) )).

cnf(u242,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k4_subset_1(X2,X1,k1_xboole_0) = X1 )).

cnf(u124,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u88,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4) )).

cnf(u87,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0) )).

cnf(u81,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k4_subset_1(X4,X3,X4) = k2_xboole_0(X3,X4) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) )).

cnf(u50,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u38,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u49,axiom,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 )).

cnf(u243,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u85,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

cnf(u111,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u74,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u296,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u69,axiom,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 )).

cnf(u122,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2))) )).

cnf(u132,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

cnf(u129,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k7_subset_1(k1_xboole_0,k1_xboole_0,X2) )).

cnf(u125,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u127,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0)) )).

cnf(u195,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) )).

cnf(u241,axiom,
    ( k4_subset_1(X1,X1,k1_xboole_0) = X1 )).

cnf(u98,axiom,
    ( k4_subset_1(X0,k1_xboole_0,X0) = X0 )).

cnf(u97,axiom,
    ( k4_subset_1(X1,X1,X1) = k2_xboole_0(X1,X1) )).

cnf(u95,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u84,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u82,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u67,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u293,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u233,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u35,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u92,axiom,
    ( k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u118,axiom,
    ( k1_xboole_0 = k3_subset_1(X1,k7_subset_1(X1,X1,k1_xboole_0)) )).

cnf(u77,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u42,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u159,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1)) )).

cnf(u131,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1)) )).

cnf(u209,axiom,
    ( k2_xboole_0(X0,X0) = k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0)) )).

cnf(u197,axiom,
    ( k2_xboole_0(X0,X0) = k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X0)) )).

cnf(u240,axiom,
    ( k2_xboole_0(X2,k1_xboole_0) = X2 )).

cnf(u73,axiom,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u123,axiom,
    ( k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) )).

cnf(u71,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:42:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (20135)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (20135)Refutation not found, incomplete strategy% (20135)------------------------------
% 0.22/0.51  % (20135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20135)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20135)Memory used [KB]: 1663
% 0.22/0.51  % (20135)Time elapsed: 0.093 s
% 0.22/0.51  % (20135)------------------------------
% 0.22/0.51  % (20135)------------------------------
% 0.22/0.52  % (20143)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (20127)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (20114)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (20125)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (20115)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (20126)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (20113)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (20125)Refutation not found, incomplete strategy% (20125)------------------------------
% 0.22/0.54  % (20125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20125)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20125)Memory used [KB]: 10618
% 0.22/0.54  % (20125)Time elapsed: 0.124 s
% 0.22/0.54  % (20125)------------------------------
% 0.22/0.54  % (20125)------------------------------
% 0.22/0.54  % (20113)Refutation not found, incomplete strategy% (20113)------------------------------
% 0.22/0.54  % (20113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20113)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20113)Memory used [KB]: 1663
% 0.22/0.54  % (20113)Time elapsed: 0.123 s
% 0.22/0.54  % (20113)------------------------------
% 0.22/0.54  % (20113)------------------------------
% 0.22/0.54  % (20115)Refutation not found, incomplete strategy% (20115)------------------------------
% 0.22/0.54  % (20115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20115)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20115)Memory used [KB]: 10746
% 0.22/0.54  % (20115)Time elapsed: 0.125 s
% 0.22/0.54  % (20115)------------------------------
% 0.22/0.54  % (20115)------------------------------
% 0.22/0.54  % (20124)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (20120)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (20129)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (20130)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (20142)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (20132)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (20121)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (20129)Refutation not found, incomplete strategy% (20129)------------------------------
% 0.22/0.55  % (20129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20137)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (20129)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  % (20117)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  
% 0.22/0.55  % (20129)Memory used [KB]: 6140
% 0.22/0.55  % (20129)Time elapsed: 0.003 s
% 0.22/0.55  % (20129)------------------------------
% 0.22/0.55  % (20129)------------------------------
% 0.22/0.55  % (20116)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (20122)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (20123)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (20123)Refutation not found, incomplete strategy% (20123)------------------------------
% 0.22/0.55  % (20123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20123)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20123)Memory used [KB]: 10618
% 0.22/0.55  % (20123)Time elapsed: 0.134 s
% 0.22/0.55  % (20123)------------------------------
% 0.22/0.55  % (20123)------------------------------
% 0.22/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.55  % (20137)Refutation not found, incomplete strategy% (20137)------------------------------
% 0.22/0.55  % (20137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20138)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (20140)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (20134)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (20121)Refutation not found, incomplete strategy% (20121)------------------------------
% 0.22/0.55  % (20121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20137)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20137)Memory used [KB]: 1791
% 0.22/0.55  % (20137)Time elapsed: 0.139 s
% 0.22/0.55  % (20137)------------------------------
% 0.22/0.55  % (20137)------------------------------
% 0.22/0.55  % (20136)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (20128)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (20141)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (20116)Refutation not found, incomplete strategy% (20116)------------------------------
% 0.22/0.56  % (20116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (20116)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (20121)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (20121)Memory used [KB]: 6268
% 0.22/0.56  % (20121)Time elapsed: 0.143 s
% 0.22/0.56  % (20121)------------------------------
% 0.22/0.56  % (20121)------------------------------
% 0.22/0.56  % (20117)Refutation not found, incomplete strategy% (20117)------------------------------
% 0.22/0.56  % (20117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (20117)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (20117)Memory used [KB]: 6268
% 0.22/0.56  % (20117)Time elapsed: 0.144 s
% 0.22/0.56  % (20117)------------------------------
% 0.22/0.56  % (20117)------------------------------
% 0.22/0.56  % (20136)Refutation not found, incomplete strategy% (20136)------------------------------
% 0.22/0.56  % (20136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (20136)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (20136)Memory used [KB]: 10746
% 0.22/0.56  % (20136)Time elapsed: 0.057 s
% 0.22/0.56  % (20136)------------------------------
% 0.22/0.56  % (20136)------------------------------
% 0.22/0.56  % (20119)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.56  % (20124)Refutation not found, incomplete strategy% (20124)------------------------------
% 0.22/0.56  % (20124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (20124)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (20124)Memory used [KB]: 10618
% 0.22/0.56  % (20124)Time elapsed: 0.148 s
% 0.22/0.56  % (20124)------------------------------
% 0.22/0.56  % (20124)------------------------------
% 0.22/0.56  % (20133)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (20122)Refutation not found, incomplete strategy% (20122)------------------------------
% 0.22/0.56  % (20122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (20122)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (20122)Memory used [KB]: 10746
% 0.22/0.56  % (20122)Time elapsed: 0.148 s
% 0.22/0.56  % (20122)------------------------------
% 0.22/0.56  % (20122)------------------------------
% 0.22/0.57  % (20131)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (20131)Refutation not found, incomplete strategy% (20131)------------------------------
% 0.22/0.57  % (20131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20131)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (20131)Memory used [KB]: 10618
% 0.22/0.57  % (20131)Time elapsed: 0.157 s
% 0.22/0.57  % (20131)------------------------------
% 0.22/0.57  % (20131)------------------------------
% 0.22/0.57  % (20134)Refutation not found, incomplete strategy% (20134)------------------------------
% 0.22/0.57  % (20134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20134)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (20134)Memory used [KB]: 10746
% 0.22/0.57  % (20134)Time elapsed: 0.159 s
% 0.22/0.57  % (20134)------------------------------
% 0.22/0.57  % (20134)------------------------------
% 0.22/0.57  % (20120)# SZS output start Saturation.
% 0.22/0.57  cnf(u72,axiom,
% 0.22/0.57      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.22/0.57  
% 0.22/0.57  cnf(u41,axiom,
% 0.22/0.57      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.22/0.57  
% 0.22/0.57  cnf(u37,negated_conjecture,
% 0.22/0.57      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.57  
% 0.22/0.57  cnf(u79,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u86,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u242,axiom,
% 0.22/0.57      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k4_subset_1(X2,X1,k1_xboole_0) = X1).
% 0.22/0.57  
% 0.22/0.57  cnf(u124,axiom,
% 0.22/0.57      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.22/0.57  
% 0.22/0.57  cnf(u88,axiom,
% 0.22/0.57      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4)).
% 0.22/0.57  
% 0.22/0.57  cnf(u87,axiom,
% 0.22/0.57      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u81,axiom,
% 0.22/0.57      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k4_subset_1(X4,X3,X4) = k2_xboole_0(X3,X4)).
% 0.22/0.57  
% 0.22/0.57  cnf(u54,axiom,
% 0.22/0.57      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.22/0.57  
% 0.22/0.57  cnf(u51,axiom,
% 0.22/0.57      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)).
% 0.22/0.57  
% 0.22/0.57  cnf(u50,axiom,
% 0.22/0.57      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.22/0.57  
% 0.22/0.57  cnf(u38,axiom,
% 0.22/0.57      r1_tarski(k1_xboole_0,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u49,axiom,
% 0.22/0.57      ~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1).
% 0.22/0.57  
% 0.22/0.57  cnf(u243,negated_conjecture,
% 0.22/0.57      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u85,negated_conjecture,
% 0.22/0.57      sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u111,negated_conjecture,
% 0.22/0.57      sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.22/0.57  
% 0.22/0.57  cnf(u74,negated_conjecture,
% 0.22/0.57      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.22/0.57  
% 0.22/0.57  cnf(u296,negated_conjecture,
% 0.22/0.57      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u69,axiom,
% 0.22/0.57      k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0).
% 0.22/0.57  
% 0.22/0.57  cnf(u122,axiom,
% 0.22/0.57      k7_subset_1(X1,k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)))).
% 0.22/0.57  
% 0.22/0.57  cnf(u132,axiom,
% 0.22/0.57      k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u129,axiom,
% 0.22/0.57      k7_subset_1(X1,k1_xboole_0,X2) = k7_subset_1(k1_xboole_0,k1_xboole_0,X2)).
% 0.22/0.57  
% 0.22/0.57  cnf(u125,negated_conjecture,
% 0.22/0.57      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u127,negated_conjecture,
% 0.22/0.57      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,k1_xboole_0))).
% 0.22/0.57  
% 0.22/0.57  cnf(u195,negated_conjecture,
% 0.22/0.57      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))).
% 0.22/0.57  
% 0.22/0.57  cnf(u241,axiom,
% 0.22/0.57      k4_subset_1(X1,X1,k1_xboole_0) = X1).
% 0.22/0.57  
% 0.22/0.57  cnf(u98,axiom,
% 0.22/0.57      k4_subset_1(X0,k1_xboole_0,X0) = X0).
% 0.22/0.57  
% 0.22/0.57  cnf(u97,axiom,
% 0.22/0.57      k4_subset_1(X1,X1,X1) = k2_xboole_0(X1,X1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u95,negated_conjecture,
% 0.22/0.57      k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.22/0.57  
% 0.22/0.57  cnf(u84,negated_conjecture,
% 0.22/0.57      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u82,negated_conjecture,
% 0.22/0.57      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u67,axiom,
% 0.22/0.57      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.22/0.57  
% 0.22/0.57  cnf(u293,axiom,
% 0.22/0.57      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u233,axiom,
% 0.22/0.57      k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u35,negated_conjecture,
% 0.22/0.57      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u92,axiom,
% 0.22/0.57      k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u118,axiom,
% 0.22/0.57      k1_xboole_0 = k3_subset_1(X1,k7_subset_1(X1,X1,k1_xboole_0))).
% 0.22/0.57  
% 0.22/0.57  cnf(u77,axiom,
% 0.22/0.57      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u42,axiom,
% 0.22/0.57      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u159,negated_conjecture,
% 0.22/0.57      k2_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(X0,k1_xboole_0,sK1))).
% 0.22/0.57  
% 0.22/0.57  cnf(u131,negated_conjecture,
% 0.22/0.57      k2_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(k1_xboole_0,k1_xboole_0,sK1))).
% 0.22/0.57  
% 0.22/0.57  cnf(u209,axiom,
% 0.22/0.57      k2_xboole_0(X0,X0) = k3_subset_1(X0,k7_subset_1(X1,k1_xboole_0,X0))).
% 0.22/0.57  
% 0.22/0.57  cnf(u197,axiom,
% 0.22/0.57      k2_xboole_0(X0,X0) = k3_subset_1(X0,k7_subset_1(X0,k1_xboole_0,X0))).
% 0.22/0.57  
% 0.22/0.57  cnf(u240,axiom,
% 0.22/0.57      k2_xboole_0(X2,k1_xboole_0) = X2).
% 0.22/0.57  
% 0.22/0.57  cnf(u73,axiom,
% 0.22/0.57      k2_xboole_0(k1_xboole_0,X0) = X0).
% 0.22/0.57  
% 0.22/0.57  cnf(u123,axiom,
% 0.22/0.57      k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)))).
% 0.22/0.57  
% 0.22/0.57  cnf(u71,negated_conjecture,
% 0.22/0.57      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.22/0.57  
% 0.22/0.57  % (20120)# SZS output end Saturation.
% 0.22/0.57  % (20120)------------------------------
% 0.22/0.57  % (20120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20120)Termination reason: Satisfiable
% 0.22/0.57  
% 0.22/0.57  % (20120)Memory used [KB]: 6396
% 0.22/0.57  % (20120)Time elapsed: 0.130 s
% 0.22/0.57  % (20120)------------------------------
% 0.22/0.57  % (20120)------------------------------
% 0.22/0.57  % (20139)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (20111)Success in time 0.204 s
%------------------------------------------------------------------------------
