%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  85 expanded)
%              Number of leaves         :    9 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 104 expanded)
%              Number of equality atoms :   43 (  94 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46])).

fof(f46,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl3_1 ),
    inference(forward_demodulation,[],[f43,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f22,f17,f19,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f43,plain,
    ( k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))),sK2)
    | spl3_1 ),
    inference(superposition,[],[f41,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X0,X2))) ),
    inference(definition_unfolding,[],[f20,f17,f17])).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f41,plain,
    ( k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f39])).

fof(f35,plain,(
    k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2))) ),
    inference(trivial_inequality_removal,[],[f34])).

fof(f34,plain,
    ( k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK1))
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2))) ),
    inference(forward_demodulation,[],[f33,f29])).

fof(f33,plain,
    ( k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))))
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2))) ),
    inference(backward_demodulation,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X0))) ),
    inference(definition_unfolding,[],[f21,f17,f17])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,
    ( k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) != k5_xboole_0(k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_zfmisc_1(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2))) ),
    inference(definition_unfolding,[],[f15,f18,f17,f27,f27,f18,f17,f27,f27])).

fof(f15,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
      | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:31:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (27999)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (27998)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (28010)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (28013)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (28005)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (28013)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f42,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl3_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    $false | spl3_1),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) | spl3_1),
% 0.22/0.48    inference(forward_demodulation,[],[f43,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f22,f17,f19,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f16,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))),sK2) | spl3_1),
% 0.22/0.48    inference(superposition,[],[f41,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X0,X2)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f20,f17,f17])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2))) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    spl3_1 <=> k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) = k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ~spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f39])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2)))),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2)))),
% 0.22/0.48    inference(forward_demodulation,[],[f33,f29])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))) | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2)))),
% 0.22/0.48    inference(backward_demodulation,[],[f30,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f21,f17,f17])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) != k5_xboole_0(k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_zfmisc_1(sK2,k2_enumset1(sK1,sK1,sK1,sK1)),k2_zfmisc_1(sK2,k2_enumset1(sK0,sK0,sK0,sK0)))) | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),sK2) != k5_xboole_0(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2),k4_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK2)))),
% 0.22/0.48    inference(definition_unfolding,[],[f15,f18,f17,f27,f27,f18,f17,f27,f27])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2))) => (k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (28013)------------------------------
% 0.22/0.48  % (28013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (28013)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (28013)Memory used [KB]: 10618
% 0.22/0.48  % (28013)Time elapsed: 0.007 s
% 0.22/0.48  % (28013)------------------------------
% 0.22/0.48  % (28013)------------------------------
% 0.22/0.48  % (28006)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (27997)Success in time 0.12 s
%------------------------------------------------------------------------------
