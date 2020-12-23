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

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   54 (  54 expanded)
%              Number of leaves         :   54 (  54 expanded)
%              Depth                    :    0
%              Number of atoms          :   69 (  69 expanded)
%              Number of equality atoms :   52 (  52 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u68,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u39,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u35,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u216,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) )).

cnf(u224,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1) )).

cnf(u226,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4) )).

cnf(u225,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0) )).

cnf(u220,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k4_subset_1(X2,X1,k1_xboole_0) = X1 )).

cnf(u218,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k4_subset_1(X4,X3,X4) )).

cnf(u95,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u94,axiom,
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

cnf(u91,axiom,
    ( k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) )).

cnf(u98,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u332,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u137,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) )).

cnf(u114,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u108,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u93,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X2) )).

cnf(u33,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u378,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u328,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u324,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u327,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u233,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

cnf(u231,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u366,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) )).

cnf(u222,axiom,
    ( k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u221,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u341,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u70,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u73,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u329,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u145,axiom,
    ( k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k5_xboole_0(X3,k7_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),X3)) )).

cnf(u189,axiom,
    ( k5_xboole_0(X3,k7_subset_1(X2,X2,X3)) = k5_xboole_0(X2,k7_subset_1(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),X2)) )).

cnf(u99,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) )).

cnf(u331,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) )).

cnf(u138,axiom,
    ( k1_xboole_0 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k5_xboole_0(X3,k7_subset_1(X2,X2,X3))))) )).

cnf(u97,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u83,axiom,
    ( k1_xboole_0 = k5_xboole_0(X2,X2) )).

cnf(u61,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u107,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u288,axiom,
    ( k4_subset_1(X0,k1_xboole_0,X0) = X0 )).

cnf(u290,axiom,
    ( k4_subset_1(X1,X1,X1) = X1 )).

cnf(u223,axiom,
    ( k4_subset_1(X1,X1,k1_xboole_0) = X1 )).

cnf(u58,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u142,axiom,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u41,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u67,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:12:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (19531)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (19546)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (19556)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (19541)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (19531)Refutation not found, incomplete strategy% (19531)------------------------------
% 0.21/0.52  % (19531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19536)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (19531)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19531)Memory used [KB]: 1663
% 0.21/0.52  % (19531)Time elapsed: 0.092 s
% 0.21/0.52  % (19531)------------------------------
% 0.21/0.52  % (19531)------------------------------
% 0.21/0.52  % (19533)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (19541)Refutation not found, incomplete strategy% (19541)------------------------------
% 0.21/0.52  % (19541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19541)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19541)Memory used [KB]: 10618
% 0.21/0.52  % (19541)Time elapsed: 0.100 s
% 0.21/0.52  % (19541)------------------------------
% 0.21/0.52  % (19541)------------------------------
% 0.21/0.52  % (19538)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (19537)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (19534)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (19546)Refutation not found, incomplete strategy% (19546)------------------------------
% 0.21/0.52  % (19546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19546)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19546)Memory used [KB]: 6140
% 0.21/0.52  % (19546)Time elapsed: 0.003 s
% 0.21/0.52  % (19546)------------------------------
% 0.21/0.52  % (19546)------------------------------
% 0.21/0.53  % (19538)Refutation not found, incomplete strategy% (19538)------------------------------
% 0.21/0.53  % (19538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19538)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19538)Memory used [KB]: 6396
% 0.21/0.53  % (19538)Time elapsed: 0.109 s
% 0.21/0.53  % (19538)------------------------------
% 0.21/0.53  % (19538)------------------------------
% 0.21/0.53  % (19533)Refutation not found, incomplete strategy% (19533)------------------------------
% 0.21/0.53  % (19533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19533)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19533)Memory used [KB]: 10874
% 0.21/0.53  % (19533)Time elapsed: 0.107 s
% 0.21/0.53  % (19533)------------------------------
% 0.21/0.53  % (19533)------------------------------
% 0.21/0.53  % (19554)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (19532)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (19535)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (19553)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (19560)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (19553)Refutation not found, incomplete strategy% (19553)------------------------------
% 0.21/0.54  % (19553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19553)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19553)Memory used [KB]: 10746
% 0.21/0.54  % (19553)Time elapsed: 0.091 s
% 0.21/0.54  % (19553)------------------------------
% 0.21/0.54  % (19553)------------------------------
% 0.21/0.54  % (19545)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (19559)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (19539)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (19540)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (19540)Refutation not found, incomplete strategy% (19540)------------------------------
% 0.21/0.54  % (19540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19540)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19540)Memory used [KB]: 10618
% 0.21/0.54  % (19540)Time elapsed: 0.122 s
% 0.21/0.54  % (19540)------------------------------
% 0.21/0.54  % (19540)------------------------------
% 0.21/0.54  % (19554)Refutation not found, incomplete strategy% (19554)------------------------------
% 0.21/0.54  % (19554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19554)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19554)Memory used [KB]: 1791
% 0.21/0.54  % (19554)Time elapsed: 0.105 s
% 0.21/0.54  % (19554)------------------------------
% 0.21/0.54  % (19554)------------------------------
% 0.21/0.54  % (19557)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (19551)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (19536)Refutation not found, incomplete strategy% (19536)------------------------------
% 0.21/0.55  % (19536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19536)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19536)Memory used [KB]: 6396
% 0.21/0.55  % (19536)Time elapsed: 0.113 s
% 0.21/0.55  % (19536)------------------------------
% 0.21/0.55  % (19536)------------------------------
% 0.21/0.55  % (19551)Refutation not found, incomplete strategy% (19551)------------------------------
% 0.21/0.55  % (19551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19551)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19551)Memory used [KB]: 10746
% 0.21/0.55  % (19551)Time elapsed: 0.127 s
% 0.21/0.55  % (19551)------------------------------
% 0.21/0.55  % (19551)------------------------------
% 0.21/0.55  % (19558)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (19552)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (19549)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (19537)# SZS output start Saturation.
% 0.21/0.55  cnf(u68,axiom,
% 0.21/0.55      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u39,axiom,
% 0.21/0.55      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u35,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u216,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u224,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u226,axiom,
% 0.21/0.55      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4)).
% 0.21/0.55  
% 0.21/0.55  cnf(u225,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u220,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k4_subset_1(X2,X1,k1_xboole_0) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u218,axiom,
% 0.21/0.55      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k4_subset_1(X4,X3,X4)).
% 0.21/0.55  
% 0.21/0.55  cnf(u95,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u94,axiom,
% 0.21/0.55      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u52,axiom,
% 0.21/0.55      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u51,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u36,axiom,
% 0.21/0.55      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u64,axiom,
% 0.21/0.55      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u69,axiom,
% 0.21/0.55      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u59,axiom,
% 0.21/0.55      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u91,axiom,
% 0.21/0.55      k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u98,negated_conjecture,
% 0.21/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u332,negated_conjecture,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u137,axiom,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u114,axiom,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u108,axiom,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u93,axiom,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u33,negated_conjecture,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u378,negated_conjecture,
% 0.21/0.55      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u328,negated_conjecture,
% 0.21/0.55      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u324,negated_conjecture,
% 0.21/0.55      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u327,negated_conjecture,
% 0.21/0.55      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u233,negated_conjecture,
% 0.21/0.55      sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u231,negated_conjecture,
% 0.21/0.55      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u366,negated_conjecture,
% 0.21/0.55      k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u222,axiom,
% 0.21/0.55      k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u221,negated_conjecture,
% 0.21/0.55      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u341,negated_conjecture,
% 0.21/0.55      sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u70,negated_conjecture,
% 0.21/0.55      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u73,axiom,
% 0.21/0.55      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u329,negated_conjecture,
% 0.21/0.55      u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u145,axiom,
% 0.21/0.55      k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k5_xboole_0(X3,k7_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),X3))).
% 0.21/0.55  
% 0.21/0.55  cnf(u189,axiom,
% 0.21/0.55      k5_xboole_0(X3,k7_subset_1(X2,X2,X3)) = k5_xboole_0(X2,k7_subset_1(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),X2))).
% 0.21/0.55  
% 0.21/0.55  cnf(u99,axiom,
% 0.21/0.55      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u331,negated_conjecture,
% 0.21/0.55      k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))).
% 0.21/0.55  
% 0.21/0.55  cnf(u138,axiom,
% 0.21/0.55      k1_xboole_0 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k5_xboole_0(X3,k7_subset_1(X2,X2,X3)))))).
% 0.21/0.55  
% 0.21/0.55  cnf(u97,axiom,
% 0.21/0.55      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 0.21/0.55  
% 0.21/0.55  cnf(u83,axiom,
% 0.21/0.55      k1_xboole_0 = k5_xboole_0(X2,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u61,axiom,
% 0.21/0.55      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u107,axiom,
% 0.21/0.55      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u288,axiom,
% 0.21/0.55      k4_subset_1(X0,k1_xboole_0,X0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u290,axiom,
% 0.21/0.55      k4_subset_1(X1,X1,X1) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u223,axiom,
% 0.21/0.55      k4_subset_1(X1,X1,k1_xboole_0) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u58,axiom,
% 0.21/0.55      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u142,axiom,
% 0.21/0.55      k5_xboole_0(k1_xboole_0,X0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u41,axiom,
% 0.21/0.55      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u67,negated_conjecture,
% 0.21/0.55      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.55  
% 0.21/0.55  % (19537)# SZS output end Saturation.
% 0.21/0.55  % (19537)------------------------------
% 0.21/0.55  % (19537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19537)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (19537)Memory used [KB]: 6524
% 0.21/0.55  % (19537)Time elapsed: 0.109 s
% 0.21/0.55  % (19537)------------------------------
% 0.21/0.55  % (19537)------------------------------
% 0.21/0.55  % (19530)Success in time 0.189 s
%------------------------------------------------------------------------------
