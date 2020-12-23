%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  36 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f31,f36])).

fof(f36,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f32])).

fof(f32,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f13,f30])).

fof(f30,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_2
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f31,plain,
    ( ~ spl4_2
    | spl4_1 ),
    inference(avatar_split_clause,[],[f26,f22,f28])).

fof(f22,plain,
    ( spl4_1
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f26,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f24,f13])).

fof(f24,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f25,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f17,f22])).

fof(f17,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))) ),
    inference(definition_unfolding,[],[f10,f15,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f12,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f12,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f14,f11,f11])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:05:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (12480)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.43  % (12480)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f25,f31,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    spl4_2),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    $false | spl4_2),
% 0.22/0.43    inference(unit_resulting_resolution,[],[f13,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))) | spl4_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    spl4_2 <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ~spl4_2 | spl4_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f26,f22,f28])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    spl4_1 <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))) | spl4_1),
% 0.22/0.43    inference(forward_demodulation,[],[f24,f13])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))) | spl4_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f22])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ~spl4_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f22])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3)))),
% 0.22/0.43    inference(definition_unfolding,[],[f10,f15,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f12,f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f14,f11,f11])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (12480)------------------------------
% 0.22/0.43  % (12480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (12480)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (12480)Memory used [KB]: 10618
% 0.22/0.43  % (12480)Time elapsed: 0.004 s
% 0.22/0.43  % (12480)------------------------------
% 0.22/0.43  % (12480)------------------------------
% 0.22/0.43  % (12462)Success in time 0.07 s
%------------------------------------------------------------------------------
