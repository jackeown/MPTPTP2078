%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:51 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  58 expanded)
%              Number of equality atoms :   23 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f21,f25,f29,f33])).

fof(f33,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f32])).

fof(f32,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f16,f31])).

fof(f31,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f30,f24])).

fof(f24,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl2_3
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f30,plain,
    ( ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_enumset1(X0,X0,X0,X1)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f28,f20])).

fof(f20,plain,
    ( ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl2_2
  <=> ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f28,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_4
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f16,plain,
    ( k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl2_1
  <=> k2_tarski(sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f29,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f12,f27])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f25,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f11,f23])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f21,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f10,f19])).

fof(f10,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f17,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f9,f14])).

fof(f9,plain,(
    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_enumset1(X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_enumset1(X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:02:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (32083)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.45  % (32083)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f17,f21,f25,f29,f33])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f32])).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    $false | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.19/0.45    inference(subsumption_resolution,[],[f16,f31])).
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) ) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.19/0.45    inference(forward_demodulation,[],[f30,f24])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | ~spl2_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f23])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    spl2_3 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_enumset1(X0,X0,X0,X1)) ) | (~spl2_2 | ~spl2_4)),
% 0.19/0.45    inference(superposition,[],[f28,f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) ) | ~spl2_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    spl2_2 <=> ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) ) | ~spl2_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f27])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    spl2_4 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) | spl2_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    spl2_1 <=> k2_tarski(sK0,sK1) = k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    spl2_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f12,f27])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    spl2_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f11,f23])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    spl2_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f10,f19])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ~spl2_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f9,f14])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f8,plain,(
% 0.19/0.45    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).
% 0.19/0.45  fof(f7,plain,(
% 0.19/0.45    ? [X0,X1] : k2_tarski(X0,X1) != k2_enumset1(X0,X0,X0,X1) => k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f6,plain,(
% 0.19/0.45    ? [X0,X1] : k2_tarski(X0,X1) != k2_enumset1(X0,X0,X0,X1)),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.19/0.45    inference(negated_conjecture,[],[f4])).
% 0.19/0.45  fof(f4,conjecture,(
% 0.19/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (32083)------------------------------
% 0.19/0.45  % (32083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (32083)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (32083)Memory used [KB]: 6012
% 0.19/0.45  % (32083)Time elapsed: 0.044 s
% 0.19/0.45  % (32083)------------------------------
% 0.19/0.45  % (32083)------------------------------
% 0.19/0.45  % (32081)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.46  % (32077)Success in time 0.105 s
%------------------------------------------------------------------------------
