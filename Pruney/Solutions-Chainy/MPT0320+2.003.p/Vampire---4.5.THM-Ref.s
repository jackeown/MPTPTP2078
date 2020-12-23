%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 115 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 139 expanded)
%              Number of equality atoms :   44 ( 120 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f57,f119])).

fof(f119,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1))
    | spl3_2 ),
    inference(forward_demodulation,[],[f116,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f19,f20,f21])).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f14,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f116,plain,
    ( k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))))
    | spl3_2 ),
    inference(superposition,[],[f34,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f18,f20,f20])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f34,plain,
    ( k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) != k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_2
  <=> k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2)
    | spl3_1 ),
    inference(forward_demodulation,[],[f54,f23])).

fof(f54,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) != k2_zfmisc_1(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),sK2)
    | spl3_1 ),
    inference(superposition,[],[f30,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f17,f20,f20])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) != k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) = k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f32,f28])).

fof(f24,plain,
    ( k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) != k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1))))
    | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) != k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f12,f15,f20,f21,f21,f15,f20,f21,f21])).

fof(f12,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
      | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:53:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (9115)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (9111)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (9110)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (9108)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (9116)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (9111)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f35,f57,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    $false | spl3_2),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) | spl3_2),
% 0.21/0.48    inference(forward_demodulation,[],[f116,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f16,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f19,f20,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f13,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f14,f15])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)))) | spl3_2),
% 0.21/0.48    inference(superposition,[],[f34,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f18,f20,f20])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) != k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1)))) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl3_2 <=> k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    $false | spl3_1),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) | spl3_1),
% 0.21/0.48    inference(forward_demodulation,[],[f54,f23])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) != k2_zfmisc_1(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),sK2) | spl3_1),
% 0.21/0.48    inference(superposition,[],[f30,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f17,f20,f20])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) != k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    spl3_1 <=> k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) = k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f32,f28])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK1)) != k3_tarski(k1_enumset1(k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK0,sK0,sK0)),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1)))) | k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),sK2) != k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK2),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 0.21/0.48    inference(definition_unfolding,[],[f12,f15,f20,f21,f21,f15,f20,f21,f21])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2))) => (k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9111)------------------------------
% 0.21/0.48  % (9111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9111)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9111)Memory used [KB]: 6140
% 0.21/0.48  % (9111)Time elapsed: 0.056 s
% 0.21/0.48  % (9111)------------------------------
% 0.21/0.48  % (9111)------------------------------
% 0.21/0.48  % (9106)Success in time 0.114 s
%------------------------------------------------------------------------------
