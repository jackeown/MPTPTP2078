%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:38 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 215 expanded)
%              Number of leaves         :   19 (  74 expanded)
%              Depth                    :   18
%              Number of atoms          :   97 ( 246 expanded)
%              Number of equality atoms :   59 ( 186 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f1208,f1212])).

fof(f1212,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f1209])).

fof(f1209,plain,
    ( $false
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f53,f1207])).

fof(f1207,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f1205])).

fof(f1205,plain,
    ( spl2_3
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f48,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f1208,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f1203,f93,f1205])).

fof(f93,plain,
    ( spl2_2
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1203,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f1202])).

fof(f1202,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl2_2 ),
    inference(forward_demodulation,[],[f1185,f447])).

fof(f447,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f445,f36])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f445,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(forward_demodulation,[],[f254,f241])).

fof(f241,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f233,f36])).

fof(f233,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f117,f226])).

fof(f226,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(global_subsumption,[],[f195,f212])).

fof(f212,plain,(
    ! [X3] :
      ( k1_xboole_0 = k4_xboole_0(X3,X3)
      | ~ r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f140,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f140,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f55,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f44,f37,f37])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f195,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f181,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f181,plain,(
    ! [X6,X7] : r1_tarski(k1_xboole_0,k5_xboole_0(X7,k4_xboole_0(k1_xboole_0,X6))) ),
    inference(superposition,[],[f167,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f167,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f114,f36])).

fof(f114,plain,(
    ! [X15,X16] : r1_tarski(k1_xboole_0,k5_xboole_0(X15,k5_xboole_0(X16,k1_xboole_0))) ),
    inference(superposition,[],[f59,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f58,f36])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f51,f38])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f117,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f49,f38])).

fof(f254,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f34,f240])).

fof(f240,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f235,f38])).

fof(f235,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f49,f226])).

fof(f1185,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | spl2_2 ),
    inference(superposition,[],[f95,f384])).

fof(f384,plain,(
    ! [X4,X5] :
      ( k5_xboole_0(X4,X5) = k4_xboole_0(X4,X5)
      | ~ r1_tarski(X5,X4) ) ),
    inference(superposition,[],[f49,f141])).

fof(f141,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f55,f54])).

fof(f95,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f96,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f27,f47,f28,f48,f47])).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:16:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (5352)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (5361)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (5346)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (5367)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (5346)Refutation not found, incomplete strategy% (5346)------------------------------
% 0.21/0.52  % (5346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5346)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5346)Memory used [KB]: 1663
% 0.21/0.52  % (5346)Time elapsed: 0.071 s
% 0.21/0.52  % (5346)------------------------------
% 0.21/0.52  % (5346)------------------------------
% 0.21/0.52  % (5369)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (5354)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (5349)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (5369)Refutation not found, incomplete strategy% (5369)------------------------------
% 0.21/0.53  % (5369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5356)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (5359)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (5351)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (5345)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (5369)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5369)Memory used [KB]: 10618
% 0.21/0.53  % (5369)Time elapsed: 0.104 s
% 0.21/0.53  % (5369)------------------------------
% 0.21/0.53  % (5369)------------------------------
% 0.21/0.53  % (5361)Refutation not found, incomplete strategy% (5361)------------------------------
% 0.21/0.53  % (5361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5361)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5361)Memory used [KB]: 10618
% 0.21/0.53  % (5361)Time elapsed: 0.114 s
% 0.21/0.53  % (5361)------------------------------
% 0.21/0.53  % (5361)------------------------------
% 0.21/0.54  % (5362)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (5362)Refutation not found, incomplete strategy% (5362)------------------------------
% 0.21/0.54  % (5362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5362)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5362)Memory used [KB]: 1663
% 0.21/0.54  % (5362)Time elapsed: 0.119 s
% 0.21/0.54  % (5362)------------------------------
% 0.21/0.54  % (5362)------------------------------
% 0.21/0.54  % (5359)Refutation not found, incomplete strategy% (5359)------------------------------
% 0.21/0.54  % (5359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5359)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5359)Memory used [KB]: 1663
% 0.21/0.54  % (5359)Time elapsed: 0.094 s
% 0.21/0.54  % (5359)------------------------------
% 0.21/0.54  % (5359)------------------------------
% 0.21/0.54  % (5353)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (5371)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (5350)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (5355)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (5348)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (5373)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (5363)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (5355)Refutation not found, incomplete strategy% (5355)------------------------------
% 0.21/0.55  % (5355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5355)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5355)Memory used [KB]: 10618
% 0.21/0.55  % (5355)Time elapsed: 0.131 s
% 0.21/0.55  % (5355)------------------------------
% 0.21/0.55  % (5355)------------------------------
% 0.21/0.55  % (5347)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (5356)Refutation not found, incomplete strategy% (5356)------------------------------
% 0.21/0.55  % (5356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5363)Refutation not found, incomplete strategy% (5363)------------------------------
% 0.21/0.55  % (5363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5363)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5363)Memory used [KB]: 1663
% 0.21/0.55  % (5363)Time elapsed: 0.126 s
% 0.21/0.55  % (5363)------------------------------
% 0.21/0.55  % (5363)------------------------------
% 0.21/0.55  % (5371)Refutation not found, incomplete strategy% (5371)------------------------------
% 0.21/0.55  % (5371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5374)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (5371)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5371)Memory used [KB]: 6140
% 0.21/0.55  % (5371)Time elapsed: 0.142 s
% 0.21/0.55  % (5371)------------------------------
% 0.21/0.55  % (5371)------------------------------
% 0.21/0.55  % (5374)Refutation not found, incomplete strategy% (5374)------------------------------
% 0.21/0.55  % (5374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5374)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5374)Memory used [KB]: 1663
% 0.21/0.55  % (5374)Time elapsed: 0.139 s
% 0.21/0.55  % (5374)------------------------------
% 0.21/0.55  % (5374)------------------------------
% 0.21/0.55  % (5365)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (5366)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (5356)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5356)Memory used [KB]: 6140
% 0.21/0.55  % (5356)Time elapsed: 0.126 s
% 0.21/0.55  % (5356)------------------------------
% 0.21/0.55  % (5356)------------------------------
% 0.21/0.56  % (5372)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (5370)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (5372)Refutation not found, incomplete strategy% (5372)------------------------------
% 0.21/0.56  % (5372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5372)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5372)Memory used [KB]: 6140
% 0.21/0.56  % (5372)Time elapsed: 0.134 s
% 0.21/0.56  % (5372)------------------------------
% 0.21/0.56  % (5372)------------------------------
% 0.21/0.56  % (5370)Refutation not found, incomplete strategy% (5370)------------------------------
% 0.21/0.56  % (5370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5370)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  % (5368)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  
% 0.21/0.56  % (5370)Memory used [KB]: 6140
% 0.21/0.56  % (5370)Time elapsed: 0.147 s
% 0.21/0.56  % (5370)------------------------------
% 0.21/0.56  % (5370)------------------------------
% 0.21/0.56  % (5364)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (5357)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (5358)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (5357)Refutation not found, incomplete strategy% (5357)------------------------------
% 0.21/0.56  % (5357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5357)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5357)Memory used [KB]: 10618
% 0.21/0.56  % (5357)Time elapsed: 0.152 s
% 0.21/0.56  % (5357)------------------------------
% 0.21/0.56  % (5357)------------------------------
% 0.21/0.56  % (5373)Refutation not found, incomplete strategy% (5373)------------------------------
% 0.21/0.56  % (5373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5373)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5373)Memory used [KB]: 10618
% 0.21/0.56  % (5373)Time elapsed: 0.149 s
% 0.21/0.56  % (5373)------------------------------
% 0.21/0.56  % (5373)------------------------------
% 0.21/0.56  % (5360)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.73/0.62  % (5368)Refutation found. Thanks to Tanya!
% 1.73/0.62  % SZS status Theorem for theBenchmark
% 1.98/0.63  % SZS output start Proof for theBenchmark
% 1.98/0.63  fof(f1213,plain,(
% 1.98/0.63    $false),
% 1.98/0.63    inference(avatar_sat_refutation,[],[f96,f1208,f1212])).
% 1.98/0.63  fof(f1212,plain,(
% 1.98/0.63    spl2_3),
% 1.98/0.63    inference(avatar_contradiction_clause,[],[f1209])).
% 1.98/0.63  fof(f1209,plain,(
% 1.98/0.63    $false | spl2_3),
% 1.98/0.63    inference(unit_resulting_resolution,[],[f53,f1207])).
% 1.98/0.63  fof(f1207,plain,(
% 1.98/0.63    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | spl2_3),
% 1.98/0.63    inference(avatar_component_clause,[],[f1205])).
% 1.98/0.63  fof(f1205,plain,(
% 1.98/0.63    spl2_3 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.98/0.63  fof(f53,plain,(
% 1.98/0.63    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.98/0.63    inference(definition_unfolding,[],[f31,f48,f47])).
% 1.98/0.63  fof(f47,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.98/0.63    inference(definition_unfolding,[],[f33,f46])).
% 1.98/0.63  fof(f46,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.98/0.63    inference(definition_unfolding,[],[f43,f45])).
% 1.98/0.63  fof(f45,plain,(
% 1.98/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f15])).
% 1.98/0.63  fof(f15,axiom,(
% 1.98/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.98/0.63  fof(f43,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f14])).
% 1.98/0.63  fof(f14,axiom,(
% 1.98/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.98/0.63  fof(f33,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f13])).
% 1.98/0.63  fof(f13,axiom,(
% 1.98/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.98/0.63  fof(f48,plain,(
% 1.98/0.63    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.98/0.63    inference(definition_unfolding,[],[f32,f47])).
% 1.98/0.63  fof(f32,plain,(
% 1.98/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f12])).
% 1.98/0.63  fof(f12,axiom,(
% 1.98/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.98/0.63  fof(f31,plain,(
% 1.98/0.63    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f18])).
% 1.98/0.63  fof(f18,axiom,(
% 1.98/0.63    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.98/0.63  fof(f1208,plain,(
% 1.98/0.63    ~spl2_3 | spl2_2),
% 1.98/0.63    inference(avatar_split_clause,[],[f1203,f93,f1205])).
% 1.98/0.63  fof(f93,plain,(
% 1.98/0.63    spl2_2 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.98/0.63  fof(f1203,plain,(
% 1.98/0.63    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | spl2_2),
% 1.98/0.63    inference(trivial_inequality_removal,[],[f1202])).
% 1.98/0.63  fof(f1202,plain,(
% 1.98/0.63    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | spl2_2),
% 1.98/0.63    inference(forward_demodulation,[],[f1185,f447])).
% 1.98/0.63  fof(f447,plain,(
% 1.98/0.63    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.98/0.63    inference(superposition,[],[f445,f36])).
% 1.98/0.63  fof(f36,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f2])).
% 1.98/0.63  fof(f2,axiom,(
% 1.98/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.98/0.63  fof(f445,plain,(
% 1.98/0.63    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) )),
% 1.98/0.63    inference(forward_demodulation,[],[f254,f241])).
% 1.98/0.63  fof(f241,plain,(
% 1.98/0.63    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.98/0.63    inference(superposition,[],[f233,f36])).
% 1.98/0.63  fof(f233,plain,(
% 1.98/0.63    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.98/0.63    inference(superposition,[],[f117,f226])).
% 1.98/0.63  fof(f226,plain,(
% 1.98/0.63    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 1.98/0.63    inference(global_subsumption,[],[f195,f212])).
% 1.98/0.63  fof(f212,plain,(
% 1.98/0.63    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | ~r1_tarski(k1_xboole_0,X3)) )),
% 1.98/0.63    inference(superposition,[],[f140,f54])).
% 1.98/0.63  fof(f54,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.98/0.63    inference(definition_unfolding,[],[f42,f37])).
% 1.98/0.63  fof(f37,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f8])).
% 1.98/0.63  fof(f8,axiom,(
% 1.98/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.98/0.63  fof(f42,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f22])).
% 1.98/0.63  fof(f22,plain,(
% 1.98/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.98/0.63    inference(ennf_transformation,[],[f6])).
% 1.98/0.63  fof(f6,axiom,(
% 1.98/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.98/0.63  fof(f140,plain,(
% 1.98/0.63    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.98/0.63    inference(superposition,[],[f55,f38])).
% 1.98/0.63  fof(f38,plain,(
% 1.98/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.98/0.63    inference(cnf_transformation,[],[f7])).
% 1.98/0.63  fof(f7,axiom,(
% 1.98/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.98/0.63  fof(f55,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.98/0.63    inference(definition_unfolding,[],[f44,f37,f37])).
% 1.98/0.63  fof(f44,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f1])).
% 1.98/0.63  fof(f1,axiom,(
% 1.98/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.98/0.63  fof(f195,plain,(
% 1.98/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.98/0.63    inference(superposition,[],[f181,f52])).
% 1.98/0.63  fof(f52,plain,(
% 1.98/0.63    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.98/0.63    inference(definition_unfolding,[],[f30,f28])).
% 1.98/0.63  fof(f28,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f11])).
% 1.98/0.63  fof(f11,axiom,(
% 1.98/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.98/0.63  fof(f30,plain,(
% 1.98/0.63    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.98/0.63    inference(cnf_transformation,[],[f5])).
% 1.98/0.63  fof(f5,axiom,(
% 1.98/0.63    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.98/0.63  fof(f181,plain,(
% 1.98/0.63    ( ! [X6,X7] : (r1_tarski(k1_xboole_0,k5_xboole_0(X7,k4_xboole_0(k1_xboole_0,X6)))) )),
% 1.98/0.63    inference(superposition,[],[f167,f49])).
% 1.98/0.63  fof(f49,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.98/0.63    inference(definition_unfolding,[],[f35,f37])).
% 1.98/0.63  fof(f35,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f4])).
% 1.98/0.63  fof(f4,axiom,(
% 1.98/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.98/0.63  fof(f167,plain,(
% 1.98/0.63    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X0)))) )),
% 1.98/0.63    inference(superposition,[],[f114,f36])).
% 1.98/0.63  fof(f114,plain,(
% 1.98/0.63    ( ! [X15,X16] : (r1_tarski(k1_xboole_0,k5_xboole_0(X15,k5_xboole_0(X16,k1_xboole_0)))) )),
% 1.98/0.63    inference(superposition,[],[f59,f34])).
% 1.98/0.63  fof(f34,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f10])).
% 1.98/0.63  fof(f10,axiom,(
% 1.98/0.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.98/0.63  fof(f59,plain,(
% 1.98/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 1.98/0.63    inference(superposition,[],[f58,f36])).
% 1.98/0.63  fof(f58,plain,(
% 1.98/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 1.98/0.63    inference(superposition,[],[f51,f38])).
% 1.98/0.63  fof(f51,plain,(
% 1.98/0.63    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.98/0.63    inference(definition_unfolding,[],[f29,f28])).
% 1.98/0.63  fof(f29,plain,(
% 1.98/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.98/0.63    inference(cnf_transformation,[],[f9])).
% 1.98/0.63  fof(f9,axiom,(
% 1.98/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.98/0.63  fof(f117,plain,(
% 1.98/0.63    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.98/0.63    inference(superposition,[],[f49,f38])).
% 1.98/0.63  fof(f254,plain,(
% 1.98/0.63    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2))) )),
% 1.98/0.63    inference(superposition,[],[f34,f240])).
% 1.98/0.63  fof(f240,plain,(
% 1.98/0.63    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 1.98/0.63    inference(forward_demodulation,[],[f235,f38])).
% 1.98/0.63  fof(f235,plain,(
% 1.98/0.63    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0))) )),
% 1.98/0.63    inference(superposition,[],[f49,f226])).
% 1.98/0.63  fof(f1185,plain,(
% 1.98/0.63    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | spl2_2),
% 1.98/0.63    inference(superposition,[],[f95,f384])).
% 1.98/0.63  fof(f384,plain,(
% 1.98/0.63    ( ! [X4,X5] : (k5_xboole_0(X4,X5) = k4_xboole_0(X4,X5) | ~r1_tarski(X5,X4)) )),
% 1.98/0.63    inference(superposition,[],[f49,f141])).
% 1.98/0.63  fof(f141,plain,(
% 1.98/0.63    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4 | ~r1_tarski(X4,X5)) )),
% 1.98/0.63    inference(superposition,[],[f55,f54])).
% 1.98/0.63  fof(f95,plain,(
% 1.98/0.63    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl2_2),
% 1.98/0.63    inference(avatar_component_clause,[],[f93])).
% 1.98/0.63  fof(f96,plain,(
% 1.98/0.63    ~spl2_2),
% 1.98/0.63    inference(avatar_split_clause,[],[f50,f93])).
% 1.98/0.63  fof(f50,plain,(
% 1.98/0.63    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.98/0.63    inference(definition_unfolding,[],[f27,f47,f28,f48,f47])).
% 1.98/0.63  fof(f27,plain,(
% 1.98/0.63    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.98/0.63    inference(cnf_transformation,[],[f24])).
% 1.98/0.63  fof(f24,plain,(
% 1.98/0.63    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.98/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 1.98/0.63  fof(f23,plain,(
% 1.98/0.63    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.98/0.63    introduced(choice_axiom,[])).
% 1.98/0.63  fof(f21,plain,(
% 1.98/0.63    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.98/0.63    inference(ennf_transformation,[],[f20])).
% 1.98/0.63  fof(f20,negated_conjecture,(
% 1.98/0.63    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.98/0.63    inference(negated_conjecture,[],[f19])).
% 1.98/0.63  fof(f19,conjecture,(
% 1.98/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.98/0.63  % SZS output end Proof for theBenchmark
% 1.98/0.63  % (5368)------------------------------
% 1.98/0.63  % (5368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.63  % (5368)Termination reason: Refutation
% 1.98/0.63  
% 1.98/0.63  % (5368)Memory used [KB]: 11641
% 1.98/0.63  % (5368)Time elapsed: 0.193 s
% 1.98/0.63  % (5368)------------------------------
% 1.98/0.63  % (5368)------------------------------
% 2.09/0.63  % (5435)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.09/0.64  % (5344)Success in time 0.262 s
%------------------------------------------------------------------------------
