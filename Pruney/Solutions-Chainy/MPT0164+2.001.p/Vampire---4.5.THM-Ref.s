%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   67 (  83 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f25,f29,f39,f47,f66,f72])).

fof(f72,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f20,f70])).

fof(f70,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f67,f38])).

fof(f38,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl5_5
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f67,plain,
    ( ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(superposition,[],[f65,f24])).

fof(f24,plain,
    ( ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl5_2
  <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f65,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_9
  <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f20,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl5_1
  <=> k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f66,plain,
    ( spl5_9
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f48,f45,f27,f64])).

fof(f27,plain,
    ( spl5_3
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f45,plain,
    ( spl5_7
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f48,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(superposition,[],[f46,f28])).

fof(f28,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f46,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f45])).

fof(f47,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f16,f45])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(f39,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f29,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k5_enumset1(X0,X0,X0,X1,X2,X3,X4)
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:42:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.40  % (20955)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.13/0.40  % (20955)Refutation not found, incomplete strategy% (20955)------------------------------
% 0.13/0.40  % (20955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.40  % (20955)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.40  
% 0.13/0.40  % (20955)Memory used [KB]: 10490
% 0.13/0.40  % (20955)Time elapsed: 0.003 s
% 0.13/0.40  % (20955)------------------------------
% 0.13/0.40  % (20955)------------------------------
% 0.20/0.43  % (20949)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.43  % (20949)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f21,f25,f29,f39,f47,f66,f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_9),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f71])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    $false | (spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_9)),
% 0.20/0.43    inference(subsumption_resolution,[],[f20,f70])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) ) | (~spl5_2 | ~spl5_5 | ~spl5_9)),
% 0.20/0.43    inference(forward_demodulation,[],[f67,f38])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) ) | ~spl5_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    spl5_5 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) ) | (~spl5_2 | ~spl5_9)),
% 0.20/0.43    inference(superposition,[],[f65,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) ) | ~spl5_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    spl5_2 <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) ) | ~spl5_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f64])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl5_9 <=> ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4) | spl5_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    spl5_1 <=> k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    spl5_9 | ~spl5_3 | ~spl5_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f48,f45,f27,f64])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    spl5_3 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    spl5_7 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) ) | (~spl5_3 | ~spl5_7)),
% 0.20/0.43    inference(superposition,[],[f46,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | ~spl5_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f27])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) ) | ~spl5_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f45])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    spl5_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f16,f45])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    spl5_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f15,f37])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    spl5_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f13,f27])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    spl5_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f12,f23])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ~spl5_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f11,f18])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k5_enumset1(X0,X0,X0,X1,X2,X3,X4) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k5_enumset1(sK0,sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 0.20/0.44    inference(negated_conjecture,[],[f6])).
% 0.20/0.44  fof(f6,conjecture,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (20949)------------------------------
% 0.20/0.44  % (20949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (20949)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (20949)Memory used [KB]: 6140
% 0.20/0.44  % (20949)Time elapsed: 0.007 s
% 0.20/0.44  % (20949)------------------------------
% 0.20/0.44  % (20949)------------------------------
% 0.20/0.44  % (20943)Success in time 0.092 s
%------------------------------------------------------------------------------
