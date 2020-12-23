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
% DateTime   : Thu Dec  3 12:41:38 EST 2020

% Result     : Theorem 3.25s
% Output     : Refutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 167 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 213 expanded)
%              Number of equality atoms :   33 ( 122 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f1231,f1340])).

fof(f1340,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f1339])).

fof(f1339,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f94,f1299])).

fof(f1299,plain,(
    ! [X72,X73] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X72,X73)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(X72,X73),k4_xboole_0(X72,X73),k4_xboole_0(X73,X72))))) ),
    inference(superposition,[],[f406,f135])).

fof(f135,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X6,X7),k4_xboole_0(X6,X7),k4_xboole_0(X7,X6))),X6) ),
    inference(forward_demodulation,[],[f120,f72])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,k3_xboole_0(X1,X0)),k4_xboole_0(X0,k3_xboole_0(X1,X0)),k4_xboole_0(k3_xboole_0(X1,X0),X0))) ),
    inference(superposition,[],[f37,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),X0))) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f120,plain,(
    ! [X6,X7] : k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X6,X7),k4_xboole_0(X6,X7),k4_xboole_0(X7,X6))),X6) = k3_tarski(k1_enumset1(k4_xboole_0(X6,k3_xboole_0(X7,X6)),k4_xboole_0(X6,k3_xboole_0(X7,X6)),k4_xboole_0(k3_xboole_0(X7,X6),X6))) ),
    inference(superposition,[],[f40,f46])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f28,f42])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_tarski(k1_enumset1(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)),k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)),k4_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X0,X1)))) = k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X2,X0))),X1) ),
    inference(definition_unfolding,[],[f33,f36,f36])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f406,plain,(
    ! [X14,X15] : r1_tarski(k1_zfmisc_1(k3_xboole_0(X14,X15)),k1_zfmisc_1(X14)) ),
    inference(superposition,[],[f44,f187])).

fof(f187,plain,(
    ! [X2,X1] : k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f51,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_zfmisc_1(X0) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f21,f23])).

fof(f94,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_1
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1231,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f1230])).

fof(f1230,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f98,f1192])).

fof(f1192,plain,(
    ! [X72,X71] : r1_tarski(k1_zfmisc_1(k4_xboole_0(X72,X71)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(X71,X72),k4_xboole_0(X71,X72),k4_xboole_0(X72,X71))))) ),
    inference(superposition,[],[f406,f130])).

fof(f130,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X7,X6),k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))),X6) ),
    inference(forward_demodulation,[],[f129,f72])).

fof(f129,plain,(
    ! [X6,X7] : k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X7,X6),k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))),X6) = k3_tarski(k1_enumset1(k4_xboole_0(X6,k3_xboole_0(X7,X6)),k4_xboole_0(X6,k3_xboole_0(X7,X6)),k4_xboole_0(k3_xboole_0(X7,X6),X6))) ),
    inference(forward_demodulation,[],[f114,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f24,f24])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f114,plain,(
    ! [X6,X7] : k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X7,X6),k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))),X6) = k3_tarski(k1_enumset1(k4_xboole_0(k3_xboole_0(X7,X6),X6),k4_xboole_0(k3_xboole_0(X7,X6),X6),k4_xboole_0(X6,k3_xboole_0(X7,X6)))) ),
    inference(superposition,[],[f40,f46])).

fof(f98,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_2
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f99,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f90,f96,f92])).

fof(f90,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f38,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(definition_unfolding,[],[f20,f35,f36])).

fof(f20,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:32:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.45  % (13941)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.47  % (13956)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.48  % (13949)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.49  % (13942)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.49  % (13950)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.49  % (13947)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.49  % (13950)Refutation not found, incomplete strategy% (13950)------------------------------
% 0.20/0.49  % (13950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13950)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13950)Memory used [KB]: 10618
% 0.20/0.49  % (13950)Time elapsed: 0.104 s
% 0.20/0.49  % (13950)------------------------------
% 0.20/0.49  % (13950)------------------------------
% 0.20/0.49  % (13939)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.49  % (13944)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (13956)Refutation not found, incomplete strategy% (13956)------------------------------
% 0.20/0.49  % (13956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13949)Refutation not found, incomplete strategy% (13949)------------------------------
% 0.20/0.49  % (13949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (13956)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (13956)Memory used [KB]: 1663
% 0.20/0.49  % (13956)Time elapsed: 0.123 s
% 0.20/0.49  % (13956)------------------------------
% 0.20/0.49  % (13956)------------------------------
% 0.20/0.50  % (13949)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13949)Memory used [KB]: 6140
% 0.20/0.50  % (13949)Time elapsed: 0.125 s
% 0.20/0.50  % (13949)------------------------------
% 0.20/0.50  % (13949)------------------------------
% 0.20/0.50  % (13962)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.50  % (13964)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (13967)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (13964)Refutation not found, incomplete strategy% (13964)------------------------------
% 0.20/0.50  % (13964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13964)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13964)Memory used [KB]: 6140
% 0.20/0.50  % (13964)Time elapsed: 0.116 s
% 0.20/0.50  % (13964)------------------------------
% 0.20/0.50  % (13964)------------------------------
% 0.20/0.50  % (13962)Refutation not found, incomplete strategy% (13962)------------------------------
% 0.20/0.50  % (13962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13962)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13962)Memory used [KB]: 10618
% 0.20/0.50  % (13962)Time elapsed: 0.107 s
% 0.20/0.50  % (13962)------------------------------
% 0.20/0.50  % (13962)------------------------------
% 0.20/0.50  % (13958)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.50  % (13939)Refutation not found, incomplete strategy% (13939)------------------------------
% 0.20/0.50  % (13939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13939)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13939)Memory used [KB]: 1663
% 0.20/0.50  % (13939)Time elapsed: 0.101 s
% 0.20/0.50  % (13939)------------------------------
% 0.20/0.50  % (13939)------------------------------
% 0.20/0.50  % (13943)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (13951)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (13953)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (13938)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (13940)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (13952)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (13966)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (13967)Refutation not found, incomplete strategy% (13967)------------------------------
% 0.20/0.51  % (13967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13967)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13967)Memory used [KB]: 1663
% 0.20/0.51  % (13967)Time elapsed: 0.125 s
% 0.20/0.51  % (13967)------------------------------
% 0.20/0.51  % (13967)------------------------------
% 0.20/0.51  % (13966)Refutation not found, incomplete strategy% (13966)------------------------------
% 0.20/0.51  % (13966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13966)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13966)Memory used [KB]: 10746
% 0.20/0.51  % (13966)Time elapsed: 0.132 s
% 0.20/0.51  % (13966)------------------------------
% 0.20/0.51  % (13966)------------------------------
% 0.20/0.51  % (13961)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (13959)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (13960)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (13965)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (13957)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (13945)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (13946)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (13955)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (13963)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (13952)Refutation not found, incomplete strategy% (13952)------------------------------
% 0.20/0.53  % (13952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13952)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13952)Memory used [KB]: 1663
% 0.20/0.53  % (13952)Time elapsed: 0.139 s
% 0.20/0.53  % (13952)------------------------------
% 0.20/0.53  % (13952)------------------------------
% 0.20/0.53  % (13954)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (13954)Refutation not found, incomplete strategy% (13954)------------------------------
% 0.20/0.53  % (13954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13954)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13954)Memory used [KB]: 10618
% 0.20/0.53  % (13954)Time elapsed: 0.117 s
% 0.20/0.53  % (13954)------------------------------
% 0.20/0.53  % (13954)------------------------------
% 0.20/0.53  % (13948)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (13963)Refutation not found, incomplete strategy% (13963)------------------------------
% 0.20/0.53  % (13963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13963)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13963)Memory used [KB]: 6140
% 0.20/0.53  % (13963)Time elapsed: 0.150 s
% 0.20/0.53  % (13963)------------------------------
% 0.20/0.53  % (13963)------------------------------
% 0.20/0.53  % (13965)Refutation not found, incomplete strategy% (13965)------------------------------
% 0.20/0.53  % (13965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13965)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13965)Memory used [KB]: 6140
% 0.20/0.53  % (13965)Time elapsed: 0.149 s
% 0.20/0.53  % (13965)------------------------------
% 0.20/0.53  % (13965)------------------------------
% 0.20/0.53  % (13948)Refutation not found, incomplete strategy% (13948)------------------------------
% 0.20/0.53  % (13948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13948)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13948)Memory used [KB]: 10746
% 0.20/0.54  % (13948)Time elapsed: 0.153 s
% 0.20/0.54  % (13948)------------------------------
% 0.20/0.54  % (13948)------------------------------
% 0.20/0.54  % (13955)Refutation not found, incomplete strategy% (13955)------------------------------
% 0.20/0.54  % (13955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13955)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13955)Memory used [KB]: 1663
% 0.20/0.54  % (13955)Time elapsed: 0.146 s
% 0.20/0.54  % (13955)------------------------------
% 0.20/0.54  % (13955)------------------------------
% 0.20/0.56  % (13941)Refutation not found, incomplete strategy% (13941)------------------------------
% 0.20/0.56  % (13941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (13941)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (13941)Memory used [KB]: 6140
% 0.20/0.58  % (13941)Time elapsed: 0.189 s
% 0.20/0.58  % (13941)------------------------------
% 0.20/0.58  % (13941)------------------------------
% 1.88/0.59  % (14017)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.88/0.59  % (14019)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.97/0.62  % (14014)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.19/0.63  % (14020)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.19/0.63  % (14022)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.19/0.63  % (13940)Refutation not found, incomplete strategy% (13940)------------------------------
% 2.19/0.63  % (13940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.63  % (13940)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.63  
% 2.19/0.63  % (13940)Memory used [KB]: 6140
% 2.19/0.63  % (13940)Time elapsed: 0.248 s
% 2.19/0.63  % (13940)------------------------------
% 2.19/0.63  % (13940)------------------------------
% 2.19/0.63  % (14022)Refutation not found, incomplete strategy% (14022)------------------------------
% 2.19/0.63  % (14022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.63  % (14022)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.63  
% 2.19/0.63  % (14022)Memory used [KB]: 10618
% 2.19/0.63  % (14022)Time elapsed: 0.117 s
% 2.19/0.63  % (14022)------------------------------
% 2.19/0.63  % (14022)------------------------------
% 2.19/0.63  % (14020)Refutation not found, incomplete strategy% (14020)------------------------------
% 2.19/0.63  % (14020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.64  % (14020)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.64  
% 2.19/0.64  % (14020)Memory used [KB]: 10618
% 2.19/0.64  % (14020)Time elapsed: 0.117 s
% 2.19/0.64  % (14020)------------------------------
% 2.19/0.64  % (14020)------------------------------
% 2.19/0.64  % (14029)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.19/0.65  % (14029)Refutation not found, incomplete strategy% (14029)------------------------------
% 2.19/0.65  % (14029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.65  % (14029)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.65  
% 2.19/0.65  % (14029)Memory used [KB]: 10618
% 2.19/0.65  % (14029)Time elapsed: 0.111 s
% 2.19/0.65  % (14029)------------------------------
% 2.19/0.65  % (14029)------------------------------
% 2.19/0.65  % (14023)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.19/0.66  % (14023)Refutation not found, incomplete strategy% (14023)------------------------------
% 2.19/0.66  % (14023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (14023)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (14023)Memory used [KB]: 1663
% 2.19/0.66  % (14023)Time elapsed: 0.121 s
% 2.19/0.66  % (14023)------------------------------
% 2.19/0.66  % (14023)------------------------------
% 2.19/0.66  % (14044)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.19/0.66  % (14035)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.19/0.66  % (14031)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.19/0.66  % (14038)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.19/0.66  % (14038)Refutation not found, incomplete strategy% (14038)------------------------------
% 2.19/0.66  % (14038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (14038)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (14038)Memory used [KB]: 10618
% 2.19/0.66  % (14038)Time elapsed: 0.113 s
% 2.19/0.66  % (14038)------------------------------
% 2.19/0.66  % (14038)------------------------------
% 2.19/0.66  % (14039)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.19/0.67  % (14045)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.19/0.67  % (13953)Refutation not found, incomplete strategy% (13953)------------------------------
% 2.19/0.67  % (13953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (14041)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.19/0.67  % (13953)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.67  
% 2.19/0.67  % (13953)Memory used [KB]: 6140
% 2.19/0.67  % (13953)Time elapsed: 0.261 s
% 2.19/0.67  % (13953)------------------------------
% 2.19/0.67  % (13953)------------------------------
% 2.19/0.68  % (14041)Refutation not found, incomplete strategy% (14041)------------------------------
% 2.19/0.68  % (14041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.68  % (14041)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.68  
% 2.19/0.68  % (14041)Memory used [KB]: 10618
% 2.19/0.68  % (14041)Time elapsed: 0.118 s
% 2.19/0.68  % (14041)------------------------------
% 2.19/0.68  % (14041)------------------------------
% 2.19/0.68  % (13946)Refutation not found, incomplete strategy% (13946)------------------------------
% 2.19/0.68  % (13946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.68  % (13946)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.68  
% 2.19/0.68  % (13946)Memory used [KB]: 6140
% 2.19/0.68  % (13946)Time elapsed: 0.286 s
% 2.19/0.68  % (13946)------------------------------
% 2.19/0.68  % (13946)------------------------------
% 2.19/0.68  % (14075)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.19/0.69  % (14045)Refutation not found, incomplete strategy% (14045)------------------------------
% 2.19/0.69  % (14045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.69  % (14045)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.69  
% 2.19/0.69  % (14045)Memory used [KB]: 10618
% 2.19/0.69  % (14045)Time elapsed: 0.125 s
% 2.19/0.69  % (14045)------------------------------
% 2.19/0.69  % (14045)------------------------------
% 2.83/0.74  % (14105)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.83/0.75  % (14107)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.83/0.77  % (14035)Refutation not found, incomplete strategy% (14035)------------------------------
% 2.83/0.77  % (14035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.77  % (14035)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.77  
% 2.83/0.77  % (14035)Memory used [KB]: 6140
% 2.83/0.77  % (14035)Time elapsed: 0.187 s
% 2.83/0.77  % (14035)------------------------------
% 2.83/0.77  % (14035)------------------------------
% 2.83/0.77  % (14108)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.83/0.77  % (14126)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.83/0.78  % (14116)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.83/0.79  % (14123)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.25/0.80  % (14075)Refutation not found, incomplete strategy% (14075)------------------------------
% 3.25/0.80  % (14075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.80  % (14075)Termination reason: Refutation not found, incomplete strategy
% 3.25/0.80  
% 3.25/0.80  % (14075)Memory used [KB]: 6140
% 3.25/0.80  % (14075)Time elapsed: 0.172 s
% 3.25/0.80  % (14075)------------------------------
% 3.25/0.80  % (14075)------------------------------
% 3.25/0.81  % (14123)Refutation not found, incomplete strategy% (14123)------------------------------
% 3.25/0.81  % (14123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.81  % (14123)Termination reason: Refutation not found, incomplete strategy
% 3.25/0.81  
% 3.25/0.81  % (14123)Memory used [KB]: 1663
% 3.25/0.81  % (14123)Time elapsed: 0.135 s
% 3.25/0.81  % (14123)------------------------------
% 3.25/0.81  % (14123)------------------------------
% 3.25/0.85  % (14108)Refutation found. Thanks to Tanya!
% 3.25/0.85  % SZS status Theorem for theBenchmark
% 3.25/0.86  % SZS output start Proof for theBenchmark
% 3.25/0.86  fof(f1344,plain,(
% 3.25/0.86    $false),
% 3.25/0.86    inference(avatar_sat_refutation,[],[f99,f1231,f1340])).
% 3.25/0.86  fof(f1340,plain,(
% 3.25/0.86    spl2_1),
% 3.25/0.86    inference(avatar_contradiction_clause,[],[f1339])).
% 3.25/0.86  fof(f1339,plain,(
% 3.25/0.86    $false | spl2_1),
% 3.25/0.86    inference(subsumption_resolution,[],[f94,f1299])).
% 3.25/0.86  fof(f1299,plain,(
% 3.25/0.86    ( ! [X72,X73] : (r1_tarski(k1_zfmisc_1(k4_xboole_0(X72,X73)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(X72,X73),k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)))))) )),
% 3.25/0.86    inference(superposition,[],[f406,f135])).
% 3.25/0.86  fof(f135,plain,(
% 3.25/0.86    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X6,X7),k4_xboole_0(X6,X7),k4_xboole_0(X7,X6))),X6)) )),
% 3.25/0.86    inference(forward_demodulation,[],[f120,f72])).
% 3.25/0.86  fof(f72,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,k3_xboole_0(X1,X0)),k4_xboole_0(X0,k3_xboole_0(X1,X0)),k4_xboole_0(k3_xboole_0(X1,X0),X0)))) )),
% 3.25/0.86    inference(superposition,[],[f37,f23])).
% 3.25/0.86  fof(f23,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.25/0.86    inference(cnf_transformation,[],[f1])).
% 3.25/0.86  fof(f1,axiom,(
% 3.25/0.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.25/0.86  fof(f37,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),X0)))) )),
% 3.25/0.86    inference(definition_unfolding,[],[f26,f36])).
% 3.25/0.86  fof(f36,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 3.25/0.86    inference(definition_unfolding,[],[f27,f35])).
% 3.25/0.86  fof(f35,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.25/0.86    inference(definition_unfolding,[],[f25,f24])).
% 3.25/0.86  fof(f24,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.25/0.86    inference(cnf_transformation,[],[f10])).
% 3.25/0.86  fof(f10,axiom,(
% 3.25/0.86    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.25/0.86  fof(f25,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.25/0.86    inference(cnf_transformation,[],[f11])).
% 3.25/0.86  fof(f11,axiom,(
% 3.25/0.86    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.25/0.86  fof(f27,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.25/0.86    inference(cnf_transformation,[],[f2])).
% 3.25/0.86  fof(f2,axiom,(
% 3.25/0.86    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 3.25/0.86  fof(f26,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.25/0.86    inference(cnf_transformation,[],[f4])).
% 3.25/0.86  fof(f4,axiom,(
% 3.25/0.86    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.25/0.86  fof(f120,plain,(
% 3.25/0.86    ( ! [X6,X7] : (k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X6,X7),k4_xboole_0(X6,X7),k4_xboole_0(X7,X6))),X6) = k3_tarski(k1_enumset1(k4_xboole_0(X6,k3_xboole_0(X7,X6)),k4_xboole_0(X6,k3_xboole_0(X7,X6)),k4_xboole_0(k3_xboole_0(X7,X6),X6)))) )),
% 3.25/0.86    inference(superposition,[],[f40,f46])).
% 3.25/0.86  fof(f46,plain,(
% 3.25/0.86    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.25/0.86    inference(resolution,[],[f28,f42])).
% 3.25/0.86  fof(f42,plain,(
% 3.25/0.86    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.25/0.86    inference(equality_resolution,[],[f31])).
% 3.25/0.86  fof(f31,plain,(
% 3.25/0.86    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.25/0.86    inference(cnf_transformation,[],[f3])).
% 3.25/0.86  fof(f3,axiom,(
% 3.25/0.86    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.25/0.86  fof(f28,plain,(
% 3.25/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.25/0.86    inference(cnf_transformation,[],[f16])).
% 3.25/0.86  fof(f16,plain,(
% 3.25/0.86    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.25/0.86    inference(ennf_transformation,[],[f7])).
% 3.25/0.86  fof(f7,axiom,(
% 3.25/0.86    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.25/0.86  fof(f40,plain,(
% 3.25/0.86    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)),k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)),k4_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X0,X1)))) = k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X0,X2),k4_xboole_0(X0,X2),k4_xboole_0(X2,X0))),X1)) )),
% 3.25/0.86    inference(definition_unfolding,[],[f33,f36,f36])).
% 3.25/0.86  fof(f33,plain,(
% 3.25/0.86    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 3.25/0.86    inference(cnf_transformation,[],[f5])).
% 3.25/0.86  fof(f5,axiom,(
% 3.25/0.86    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 3.25/0.86  fof(f406,plain,(
% 3.25/0.86    ( ! [X14,X15] : (r1_tarski(k1_zfmisc_1(k3_xboole_0(X14,X15)),k1_zfmisc_1(X14))) )),
% 3.25/0.86    inference(superposition,[],[f44,f187])).
% 3.25/0.86  fof(f187,plain,(
% 3.25/0.86    ( ! [X2,X1] : (k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))) )),
% 3.25/0.86    inference(resolution,[],[f51,f21])).
% 3.25/0.86  fof(f21,plain,(
% 3.25/0.86    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.25/0.86    inference(cnf_transformation,[],[f6])).
% 3.25/0.86  fof(f6,axiom,(
% 3.25/0.86    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.25/0.86  fof(f51,plain,(
% 3.25/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_zfmisc_1(X0) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))) )),
% 3.25/0.86    inference(resolution,[],[f29,f28])).
% 3.25/0.86  fof(f29,plain,(
% 3.25/0.86    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.25/0.86    inference(cnf_transformation,[],[f17])).
% 3.25/0.86  fof(f17,plain,(
% 3.25/0.86    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.25/0.86    inference(ennf_transformation,[],[f12])).
% 3.25/0.86  fof(f12,axiom,(
% 3.25/0.86    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 3.25/0.86  fof(f44,plain,(
% 3.25/0.86    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 3.25/0.86    inference(superposition,[],[f21,f23])).
% 3.25/0.86  fof(f94,plain,(
% 3.25/0.86    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl2_1),
% 3.25/0.86    inference(avatar_component_clause,[],[f92])).
% 3.25/0.86  fof(f92,plain,(
% 3.25/0.86    spl2_1 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 3.25/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.25/0.86  fof(f1231,plain,(
% 3.25/0.86    spl2_2),
% 3.25/0.86    inference(avatar_contradiction_clause,[],[f1230])).
% 3.25/0.86  fof(f1230,plain,(
% 3.25/0.86    $false | spl2_2),
% 3.25/0.86    inference(subsumption_resolution,[],[f98,f1192])).
% 3.25/0.86  fof(f1192,plain,(
% 3.25/0.86    ( ! [X72,X71] : (r1_tarski(k1_zfmisc_1(k4_xboole_0(X72,X71)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(X71,X72),k4_xboole_0(X71,X72),k4_xboole_0(X72,X71)))))) )),
% 3.25/0.86    inference(superposition,[],[f406,f130])).
% 3.25/0.86  fof(f130,plain,(
% 3.25/0.86    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X7,X6),k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))),X6)) )),
% 3.25/0.86    inference(forward_demodulation,[],[f129,f72])).
% 3.25/0.86  fof(f129,plain,(
% 3.25/0.86    ( ! [X6,X7] : (k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X7,X6),k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))),X6) = k3_tarski(k1_enumset1(k4_xboole_0(X6,k3_xboole_0(X7,X6)),k4_xboole_0(X6,k3_xboole_0(X7,X6)),k4_xboole_0(k3_xboole_0(X7,X6),X6)))) )),
% 3.25/0.86    inference(forward_demodulation,[],[f114,f39])).
% 3.25/0.86  fof(f39,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.25/0.86    inference(definition_unfolding,[],[f22,f24,f24])).
% 3.25/0.86  fof(f22,plain,(
% 3.25/0.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.25/0.86    inference(cnf_transformation,[],[f9])).
% 3.25/0.86  fof(f9,axiom,(
% 3.25/0.86    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.25/0.86  fof(f114,plain,(
% 3.25/0.86    ( ! [X6,X7] : (k3_xboole_0(k3_tarski(k1_enumset1(k4_xboole_0(X7,X6),k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))),X6) = k3_tarski(k1_enumset1(k4_xboole_0(k3_xboole_0(X7,X6),X6),k4_xboole_0(k3_xboole_0(X7,X6),X6),k4_xboole_0(X6,k3_xboole_0(X7,X6))))) )),
% 3.25/0.86    inference(superposition,[],[f40,f46])).
% 3.25/0.86  fof(f98,plain,(
% 3.25/0.86    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl2_2),
% 3.25/0.86    inference(avatar_component_clause,[],[f96])).
% 3.25/0.86  fof(f96,plain,(
% 3.25/0.86    spl2_2 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 3.25/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.25/0.86  fof(f99,plain,(
% 3.25/0.86    ~spl2_1 | ~spl2_2),
% 3.25/0.86    inference(avatar_split_clause,[],[f90,f96,f92])).
% 3.25/0.86  fof(f90,plain,(
% 3.25/0.86    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 3.25/0.86    inference(resolution,[],[f38,f41])).
% 3.25/0.86  fof(f41,plain,(
% 3.25/0.86    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.25/0.86    inference(definition_unfolding,[],[f34,f35])).
% 3.25/0.86  fof(f34,plain,(
% 3.25/0.86    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 3.25/0.86    inference(cnf_transformation,[],[f19])).
% 3.25/0.86  fof(f19,plain,(
% 3.25/0.86    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.25/0.86    inference(flattening,[],[f18])).
% 3.25/0.86  fof(f18,plain,(
% 3.25/0.86    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.25/0.86    inference(ennf_transformation,[],[f8])).
% 3.25/0.86  fof(f8,axiom,(
% 3.25/0.86    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 3.25/0.86  fof(f38,plain,(
% 3.25/0.86    ~r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))),k1_zfmisc_1(k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 3.25/0.86    inference(definition_unfolding,[],[f20,f35,f36])).
% 3.25/0.86  fof(f20,plain,(
% 3.25/0.86    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.25/0.86    inference(cnf_transformation,[],[f15])).
% 3.25/0.86  fof(f15,plain,(
% 3.25/0.86    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 3.25/0.86    inference(ennf_transformation,[],[f14])).
% 3.25/0.86  fof(f14,negated_conjecture,(
% 3.25/0.86    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 3.25/0.86    inference(negated_conjecture,[],[f13])).
% 3.25/0.86  fof(f13,conjecture,(
% 3.25/0.86    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 3.25/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 3.25/0.86  % SZS output end Proof for theBenchmark
% 3.25/0.86  % (14108)------------------------------
% 3.25/0.86  % (14108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.86  % (14108)Termination reason: Refutation
% 3.25/0.86  
% 3.25/0.86  % (14108)Memory used [KB]: 7547
% 3.25/0.86  % (14108)Time elapsed: 0.198 s
% 3.25/0.86  % (14108)------------------------------
% 3.25/0.86  % (14108)------------------------------
% 3.25/0.86  % (14105)Refutation not found, incomplete strategy% (14105)------------------------------
% 3.25/0.86  % (14105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.86  % (14105)Termination reason: Refutation not found, incomplete strategy
% 3.25/0.86  
% 3.25/0.86  % (14105)Memory used [KB]: 6140
% 3.25/0.86  % (14105)Time elapsed: 0.197 s
% 3.25/0.86  % (14105)------------------------------
% 3.25/0.86  % (14105)------------------------------
% 3.25/0.87  % (13937)Success in time 0.533 s
%------------------------------------------------------------------------------
