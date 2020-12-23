%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  94 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  99 expanded)
%              Number of equality atoms :   33 (  91 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f51])).

fof(f51,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f43])).

fof(f43,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f33,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) ),
    inference(superposition,[],[f29,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f16,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f19,f23,f15])).

fof(f15,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X0,X1)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))))) ),
    inference(definition_unfolding,[],[f22,f26,f23,f24])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f21,f23,f24])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_enumset1)).

fof(f33,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_1
  <=> k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f28,f31])).

fof(f28,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f14,f24,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f20,f23,f15,f24])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f14,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:52:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.44  % (23202)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (23202)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f34,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl3_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    $false | spl3_1),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f33,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))))) )),
% 0.21/0.46    inference(superposition,[],[f29,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f16,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f19,f23,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f18,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X0,X1)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f22,f26,f23,f24])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X0,X1))))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f21,f23,f24])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_enumset1)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0)))) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    spl3_1 <=> k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f31])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k3_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK2),k3_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),k2_tarski(sK0,sK0))))),
% 0.21/0.46    inference(definition_unfolding,[],[f14,f24,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X0,X0))))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f20,f23,f15,f24])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.46    inference(negated_conjecture,[],[f9])).
% 0.21/0.46  fof(f9,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (23202)------------------------------
% 0.21/0.46  % (23202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (23202)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (23202)Memory used [KB]: 10746
% 0.21/0.46  % (23202)Time elapsed: 0.047 s
% 0.21/0.46  % (23202)------------------------------
% 0.21/0.46  % (23202)------------------------------
% 0.21/0.46  % (23200)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (23192)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (23184)Success in time 0.106 s
%------------------------------------------------------------------------------
