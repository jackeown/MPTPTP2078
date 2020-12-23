%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  75 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  92 expanded)
%              Number of equality atoms :   34 (  74 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f90,f94])).

fof(f94,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl4_2 ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3))
    | spl4_2 ),
    inference(forward_demodulation,[],[f91,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) ),
    inference(definition_unfolding,[],[f15,f14,f22,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f13,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f91,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_zfmisc_1(k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK3))
    | spl4_2 ),
    inference(superposition,[],[f89,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f89,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_2
  <=> k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) = k2_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f90,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f85,f28,f87])).

fof(f28,plain,
    ( spl4_1
  <=> k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) = k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k1_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f85,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3)))
    | spl4_1 ),
    inference(forward_demodulation,[],[f82,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f18,f22,f14,f14])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f82,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3)))
    | spl4_1 ),
    inference(backward_demodulation,[],[f30,f26])).

fof(f30,plain,
    ( k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k1_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f31,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f23,f28])).

fof(f23,plain,(
    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k1_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) ),
    inference(definition_unfolding,[],[f12,f14,f14,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f20,f14,f14])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f12,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
   => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:05:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (14047)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (14051)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (14060)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (14055)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (14051)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f31,f90,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    spl4_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    $false | spl4_2),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f92])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) | spl4_2),
% 0.22/0.48    inference(forward_demodulation,[],[f91,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f15,f14,f22,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f13,f14])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_zfmisc_1(k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)),k1_enumset1(sK2,sK2,sK3)) | spl4_2),
% 0.22/0.48    inference(superposition,[],[f89,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3))) | spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f87])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl4_2 <=> k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) = k2_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ~spl4_2 | spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f85,f28,f87])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    spl4_1 <=> k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) = k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k1_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3))) | spl4_1),
% 0.22/0.48    inference(forward_demodulation,[],[f82,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)) = k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f18,f22,f14,f14])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),k1_enumset1(sK2,sK2,sK3))) | spl4_1),
% 0.22/0.48    inference(backward_demodulation,[],[f30,f26])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k1_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))) | spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f28])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ~spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f23,f28])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK3)) != k2_xboole_0(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k1_enumset1(k4_tarski(sK1,sK2),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)))),
% 0.22/0.48    inference(definition_unfolding,[],[f12,f14,f14,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f20,f14,f14])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (14051)------------------------------
% 0.22/0.48  % (14051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (14051)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (14051)Memory used [KB]: 6140
% 0.22/0.48  % (14051)Time elapsed: 0.054 s
% 0.22/0.48  % (14051)------------------------------
% 0.22/0.48  % (14051)------------------------------
% 0.22/0.48  % (14044)Success in time 0.114 s
%------------------------------------------------------------------------------
