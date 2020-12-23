%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:37 EST 2020

% Result     : CounterSatisfiable 1.53s
% Output     : Saturation 1.67s
% Verified   : 
% Statistics : Number of clauses        :   51 (  51 expanded)
%              Number of leaves         :   51 (  51 expanded)
%              Depth                    :    0
%              Number of atoms          :   66 (  66 expanded)
%              Number of equality atoms :   49 (  49 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u68,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u39,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u35,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u191,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) )).

cnf(u199,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1) )).

cnf(u201,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4) )).

cnf(u200,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0) )).

cnf(u195,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k4_subset_1(X2,X1,k1_xboole_0) = X1 )).

cnf(u193,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k4_subset_1(X4,X3,X4) = k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) )).

cnf(u81,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u80,axiom,
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

cnf(u36,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u64,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u69,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

cnf(u59,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u152,axiom,
    ( k1_setfam_1(k2_tarski(X3,k7_subset_1(X3,X3,X4))) = k7_subset_1(X3,X3,k1_setfam_1(k2_tarski(X3,X4))) )).

cnf(u131,axiom,
    ( k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k2_tarski(X2,X3)) )).

cnf(u84,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u139,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u79,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X2) )).

cnf(u33,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u77,axiom,
    ( k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) )).

cnf(u235,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u231,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u234,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u208,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

cnf(u206,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u248,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) )).

cnf(u197,axiom,
    ( k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u196,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u258,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) )).

cnf(u239,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u70,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u73,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u237,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u236,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) )).

cnf(u161,axiom,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k2_tarski(X0,X1)))) )).

cnf(u138,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,X1) )).

cnf(u156,axiom,
    ( k5_xboole_0(X3,k7_subset_1(k7_subset_1(X3,X3,X4),k7_subset_1(X3,X3,X4),X3)) = k5_xboole_0(k7_subset_1(X3,X3,X4),k1_setfam_1(k2_tarski(X3,X4))) )).

cnf(u85,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) )).

cnf(u61,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u93,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u219,axiom,
    ( k4_subset_1(X0,k1_xboole_0,X0) = X0 )).

cnf(u221,axiom,
    ( k4_subset_1(X1,X1,X1) = X1 )).

cnf(u198,axiom,
    ( k4_subset_1(X1,X1,k1_xboole_0) = X1 )).

cnf(u58,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u104,axiom,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u41,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u67,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (22702)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (22702)Refutation not found, incomplete strategy% (22702)------------------------------
% 0.22/0.51  % (22702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22727)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (22719)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (22698)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (22702)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22702)Memory used [KB]: 6268
% 0.22/0.51  % (22702)Time elapsed: 0.089 s
% 0.22/0.51  % (22702)------------------------------
% 0.22/0.51  % (22702)------------------------------
% 0.22/0.52  % (22719)Refutation not found, incomplete strategy% (22719)------------------------------
% 0.22/0.52  % (22719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22719)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22719)Memory used [KB]: 1791
% 0.22/0.52  % (22719)Time elapsed: 0.101 s
% 0.22/0.52  % (22719)------------------------------
% 0.22/0.52  % (22719)------------------------------
% 0.22/0.52  % (22699)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (22701)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (22703)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (22721)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (22721)Refutation not found, incomplete strategy% (22721)------------------------------
% 0.22/0.53  % (22721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22721)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22721)Memory used [KB]: 1791
% 0.22/0.53  % (22721)Time elapsed: 0.088 s
% 0.22/0.53  % (22721)------------------------------
% 0.22/0.53  % (22721)------------------------------
% 0.22/0.53  % (22724)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (22718)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (22698)Refutation not found, incomplete strategy% (22698)------------------------------
% 0.22/0.53  % (22698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22698)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22698)Memory used [KB]: 1663
% 0.22/0.53  % (22698)Time elapsed: 0.128 s
% 0.22/0.53  % (22698)------------------------------
% 0.22/0.53  % (22698)------------------------------
% 0.22/0.53  % (22708)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (22723)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (22722)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (22713)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (22726)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (22713)Refutation not found, incomplete strategy% (22713)------------------------------
% 0.22/0.54  % (22713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22713)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22713)Memory used [KB]: 6140
% 0.22/0.54  % (22713)Time elapsed: 0.001 s
% 0.22/0.54  % (22713)------------------------------
% 0.22/0.54  % (22713)------------------------------
% 0.22/0.54  % (22700)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (22716)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (22717)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (22710)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (22705)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (22712)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (22701)Refutation not found, incomplete strategy% (22701)------------------------------
% 0.22/0.55  % (22701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22701)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22701)Memory used [KB]: 10874
% 0.22/0.55  % (22701)Time elapsed: 0.142 s
% 0.22/0.55  % (22701)------------------------------
% 0.22/0.55  % (22701)------------------------------
% 0.22/0.55  % (22715)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (22714)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (22715)Refutation not found, incomplete strategy% (22715)------------------------------
% 0.22/0.55  % (22715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22715)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22715)Memory used [KB]: 10618
% 0.22/0.55  % (22715)Time elapsed: 0.139 s
% 0.22/0.55  % (22715)------------------------------
% 0.22/0.55  % (22715)------------------------------
% 0.22/0.55  % (22725)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (22707)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (22707)Refutation not found, incomplete strategy% (22707)------------------------------
% 0.22/0.55  % (22707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22707)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22707)Memory used [KB]: 10618
% 0.22/0.55  % (22707)Time elapsed: 0.141 s
% 0.22/0.55  % (22707)------------------------------
% 0.22/0.55  % (22707)------------------------------
% 0.22/0.55  % (22706)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (22711)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (22724)Refutation not found, incomplete strategy% (22724)------------------------------
% 0.22/0.55  % (22724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22724)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22724)Memory used [KB]: 11001
% 0.22/0.55  % (22724)Time elapsed: 0.149 s
% 0.22/0.55  % (22724)------------------------------
% 0.22/0.55  % (22724)------------------------------
% 0.22/0.56  % (22708)Refutation not found, incomplete strategy% (22708)------------------------------
% 0.22/0.56  % (22708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (22708)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (22708)Memory used [KB]: 10618
% 0.22/0.56  % (22708)Time elapsed: 0.153 s
% 0.22/0.56  % (22708)------------------------------
% 0.22/0.56  % (22708)------------------------------
% 1.53/0.56  % (22709)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.56  % (22704)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.56  % (22706)Refutation not found, incomplete strategy% (22706)------------------------------
% 1.53/0.56  % (22706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22706)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22706)Memory used [KB]: 10746
% 1.53/0.56  % (22706)Time elapsed: 0.153 s
% 1.53/0.56  % (22706)------------------------------
% 1.53/0.56  % (22706)------------------------------
% 1.53/0.56  % (22709)Refutation not found, incomplete strategy% (22709)------------------------------
% 1.53/0.56  % (22709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22709)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22709)Memory used [KB]: 10618
% 1.53/0.56  % (22709)Time elapsed: 0.152 s
% 1.53/0.56  % (22709)------------------------------
% 1.53/0.56  % (22709)------------------------------
% 1.53/0.56  % (22718)Refutation not found, incomplete strategy% (22718)------------------------------
% 1.53/0.56  % (22718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (22718)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (22718)Memory used [KB]: 10746
% 1.53/0.56  % (22718)Time elapsed: 0.152 s
% 1.53/0.56  % (22718)------------------------------
% 1.53/0.56  % (22718)------------------------------
% 1.53/0.57  % SZS status CounterSatisfiable for theBenchmark
% 1.53/0.57  % (22710)Refutation not found, incomplete strategy% (22710)------------------------------
% 1.53/0.57  % (22710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (22710)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (22710)Memory used [KB]: 6268
% 1.53/0.57  % (22710)Time elapsed: 0.146 s
% 1.53/0.57  % (22710)------------------------------
% 1.53/0.57  % (22710)------------------------------
% 1.67/0.58  % (22720)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.67/0.58  % (22704)# SZS output start Saturation.
% 1.67/0.58  cnf(u68,axiom,
% 1.67/0.58      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.67/0.58  
% 1.67/0.58  cnf(u39,axiom,
% 1.67/0.58      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 1.67/0.58  
% 1.67/0.58  cnf(u35,negated_conjecture,
% 1.67/0.58      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.67/0.58  
% 1.67/0.58  cnf(u191,negated_conjecture,
% 1.67/0.58      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))).
% 1.67/0.58  
% 1.67/0.58  cnf(u199,negated_conjecture,
% 1.67/0.58      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1)).
% 1.67/0.58  
% 1.67/0.58  cnf(u201,axiom,
% 1.67/0.58      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4)).
% 1.67/0.58  
% 1.67/0.58  cnf(u200,axiom,
% 1.67/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0)).
% 1.67/0.58  
% 1.67/0.58  cnf(u195,axiom,
% 1.67/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k4_subset_1(X2,X1,k1_xboole_0) = X1).
% 1.67/0.58  
% 1.67/0.58  cnf(u193,axiom,
% 1.67/0.58      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k4_subset_1(X4,X3,X4) = k5_xboole_0(X3,k7_subset_1(X4,X4,X3))).
% 1.67/0.58  
% 1.67/0.58  cnf(u81,axiom,
% 1.67/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.67/0.58  
% 1.67/0.58  cnf(u80,axiom,
% 1.67/0.58      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1))).
% 1.67/0.58  
% 1.67/0.58  cnf(u52,axiom,
% 1.67/0.58      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)).
% 1.67/0.58  
% 1.67/0.58  cnf(u51,axiom,
% 1.67/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 1.67/0.58  
% 1.67/0.58  cnf(u36,axiom,
% 1.67/0.58      r1_tarski(k1_xboole_0,X0)).
% 1.67/0.58  
% 1.67/0.58  cnf(u64,axiom,
% 1.67/0.58      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 1.67/0.58  
% 1.67/0.58  cnf(u69,axiom,
% 1.67/0.58      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 1.67/0.58  
% 1.67/0.58  cnf(u59,axiom,
% 1.67/0.58      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 1.67/0.58  
% 1.67/0.58  cnf(u152,axiom,
% 1.67/0.58      k1_setfam_1(k2_tarski(X3,k7_subset_1(X3,X3,X4))) = k7_subset_1(X3,X3,k1_setfam_1(k2_tarski(X3,X4)))).
% 1.67/0.58  
% 1.67/0.58  cnf(u131,axiom,
% 1.67/0.58      k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k2_tarski(X2,X3))).
% 1.67/0.58  
% 1.67/0.58  cnf(u84,negated_conjecture,
% 1.67/0.58      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.67/0.58  
% 1.67/0.58  cnf(u139,axiom,
% 1.67/0.58      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 1.67/0.58  
% 1.67/0.58  cnf(u79,axiom,
% 1.67/0.58      k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X2)).
% 1.67/0.58  
% 1.67/0.58  cnf(u33,negated_conjecture,
% 1.67/0.58      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.67/0.58  
% 1.67/0.58  cnf(u77,axiom,
% 1.67/0.58      k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4)))).
% 1.67/0.58  
% 1.67/0.58  cnf(u235,negated_conjecture,
% 1.67/0.58      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.67/0.58  
% 1.67/0.58  cnf(u231,negated_conjecture,
% 1.67/0.58      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 1.67/0.58  
% 1.67/0.58  cnf(u234,negated_conjecture,
% 1.67/0.58      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 1.67/0.58  
% 1.67/0.58  cnf(u208,negated_conjecture,
% 1.67/0.58      sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)).
% 1.67/0.58  
% 1.67/0.58  cnf(u206,negated_conjecture,
% 1.67/0.58      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.67/0.58  
% 1.67/0.58  cnf(u248,negated_conjecture,
% 1.67/0.58      k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0)).
% 1.67/0.58  
% 1.67/0.58  cnf(u197,axiom,
% 1.67/0.58      k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 1.67/0.58  
% 1.67/0.58  cnf(u196,negated_conjecture,
% 1.67/0.58      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 1.67/0.58  
% 1.67/0.58  cnf(u258,negated_conjecture,
% 1.67/0.58      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))).
% 1.67/0.58  
% 1.67/0.58  cnf(u239,negated_conjecture,
% 1.67/0.58      sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 1.67/0.58  
% 1.67/0.58  cnf(u70,negated_conjecture,
% 1.67/0.58      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.67/0.58  
% 1.67/0.58  cnf(u73,axiom,
% 1.67/0.58      k1_xboole_0 = k3_subset_1(X0,X0)).
% 1.67/0.58  
% 1.67/0.58  cnf(u237,negated_conjecture,
% 1.67/0.58      u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 1.67/0.58  
% 1.67/0.58  cnf(u236,negated_conjecture,
% 1.67/0.58      u1_struct_0(sK0) = k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0)))).
% 1.67/0.58  
% 1.67/0.58  cnf(u161,axiom,
% 1.67/0.58      k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k2_tarski(X0,X1))))).
% 1.67/0.58  
% 1.67/0.58  cnf(u138,axiom,
% 1.67/0.58      k1_xboole_0 = k5_xboole_0(X1,X1)).
% 1.67/0.58  
% 1.67/0.58  cnf(u156,axiom,
% 1.67/0.58      k5_xboole_0(X3,k7_subset_1(k7_subset_1(X3,X3,X4),k7_subset_1(X3,X3,X4),X3)) = k5_xboole_0(k7_subset_1(X3,X3,X4),k1_setfam_1(k2_tarski(X3,X4)))).
% 1.67/0.58  
% 1.67/0.58  cnf(u85,axiom,
% 1.67/0.58      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1))).
% 1.67/0.58  
% 1.67/0.58  cnf(u61,axiom,
% 1.67/0.58      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 1.67/0.58  
% 1.67/0.58  cnf(u93,axiom,
% 1.67/0.58      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.67/0.58  
% 1.67/0.58  cnf(u219,axiom,
% 1.67/0.58      k4_subset_1(X0,k1_xboole_0,X0) = X0).
% 1.67/0.58  
% 1.67/0.58  cnf(u221,axiom,
% 1.67/0.58      k4_subset_1(X1,X1,X1) = X1).
% 1.67/0.58  
% 1.67/0.58  cnf(u198,axiom,
% 1.67/0.58      k4_subset_1(X1,X1,k1_xboole_0) = X1).
% 1.67/0.58  
% 1.67/0.58  cnf(u58,axiom,
% 1.67/0.58      k3_subset_1(X0,k1_xboole_0) = X0).
% 1.67/0.58  
% 1.67/0.58  cnf(u104,axiom,
% 1.67/0.58      k5_xboole_0(k1_xboole_0,X0) = X0).
% 1.67/0.58  
% 1.67/0.58  cnf(u41,axiom,
% 1.67/0.58      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.67/0.58  
% 1.67/0.58  cnf(u67,negated_conjecture,
% 1.67/0.58      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.67/0.58  
% 1.67/0.58  % (22704)# SZS output end Saturation.
% 1.67/0.58  % (22704)------------------------------
% 1.67/0.58  % (22704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (22704)Termination reason: Satisfiable
% 1.67/0.58  
% 1.67/0.58  % (22704)Memory used [KB]: 6396
% 1.67/0.58  % (22704)Time elapsed: 0.136 s
% 1.67/0.58  % (22704)------------------------------
% 1.67/0.58  % (22704)------------------------------
% 1.67/0.59  % (22697)Success in time 0.213 s
%------------------------------------------------------------------------------
