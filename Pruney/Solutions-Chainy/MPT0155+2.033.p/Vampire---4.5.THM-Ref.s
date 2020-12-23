%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  32 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  38 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f26])).

fof(f26,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f25])).

fof(f25,plain,
    ( $false
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f24])).

fof(f24,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))
    | spl3_1 ),
    inference(superposition,[],[f21,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f21,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl3_1
  <=> k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f22,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f19])).

fof(f17,plain,(
    k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))) ),
    inference(definition_unfolding,[],[f10,f15,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3))) ),
    inference(definition_unfolding,[],[f14,f11,f15])).

fof(f11,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f13,f11])).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f10,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (21924)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (21924)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f22,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    $false | spl3_1),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) | spl3_1),
% 0.20/0.46    inference(superposition,[],[f21,f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))) | spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    spl3_1 <=> k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ~spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f17,f19])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) != k2_xboole_0(k2_tarski(sK0,sK0),k2_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),
% 0.20/0.46    inference(definition_unfolding,[],[f10,f15,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X0),k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f14,f11,f15])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f13,f11])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (21924)------------------------------
% 0.20/0.46  % (21924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (21924)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (21924)Memory used [KB]: 6012
% 0.20/0.46  % (21924)Time elapsed: 0.054 s
% 0.20/0.46  % (21924)------------------------------
% 0.20/0.46  % (21924)------------------------------
% 0.20/0.46  % (21916)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (21913)Success in time 0.108 s
%------------------------------------------------------------------------------
