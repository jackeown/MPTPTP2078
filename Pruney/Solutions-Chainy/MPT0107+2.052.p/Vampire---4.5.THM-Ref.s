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
% DateTime   : Thu Dec  3 12:32:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 179 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 286 expanded)
%              Number of equality atoms :   50 ( 151 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f48,f73,f100,f243,f427,f434,f439])).

fof(f439,plain,
    ( ~ spl2_7
    | spl2_17 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl2_7
    | spl2_17 ),
    inference(unit_resulting_resolution,[],[f242,f433])).

fof(f433,plain,
    ( k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | spl2_17 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl2_17
  <=> k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f242,plain,
    ( ! [X4] : k2_xboole_0(X4,k1_xboole_0) = X4
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl2_7
  <=> ! [X4] : k2_xboole_0(X4,k1_xboole_0) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f434,plain,
    ( ~ spl2_17
    | spl2_16 ),
    inference(avatar_split_clause,[],[f429,f424,f431])).

fof(f424,plain,
    ( spl2_16
  <=> k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f429,plain,
    ( k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | spl2_16 ),
    inference(forward_demodulation,[],[f428,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f428,plain,
    ( k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_xboole_0)
    | spl2_16 ),
    inference(forward_demodulation,[],[f426,f27])).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f16,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f426,plain,
    ( k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f424])).

fof(f427,plain,(
    ~ spl2_16 ),
    inference(avatar_split_clause,[],[f24,f424])).

fof(f24,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(definition_unfolding,[],[f14,f20,f18])).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f14,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f243,plain,
    ( spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f234,f98,f241])).

fof(f98,plain,
    ( spl2_5
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f234,plain,
    ( ! [X4] : k2_xboole_0(X4,k1_xboole_0) = X4
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f233,f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f15,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f233,plain,
    ( ! [X4] : k2_xboole_0(k4_xboole_0(X4,k1_xboole_0),k4_xboole_0(k1_xboole_0,X4)) = k2_xboole_0(X4,k1_xboole_0)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f222,f99])).

fof(f99,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f222,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(k1_xboole_0,X5)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X5),X4)) ),
    inference(superposition,[],[f23,f75])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f68,f68])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f64,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f27,f27])).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f25,f27])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f100,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f76,f70,f98])).

fof(f70,plain,
    ( spl2_3
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f76,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)
    | ~ spl2_3 ),
    inference(superposition,[],[f68,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f73,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f65,f45,f70])).

fof(f45,plain,
    ( spl2_2
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f65,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f25,f47])).

fof(f47,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f48,plain,
    ( spl2_2
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f42,f38,f45])).

fof(f38,plain,
    ( spl2_1
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f42,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f40,f22])).

fof(f40,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f41,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f36,f38])).

fof(f36,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f32,f27])).

fof(f32,plain,(
    ! [X2,X3] : r1_tarski(k1_xboole_0,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f16,f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (27555)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.43  % (27555)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f440,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f41,f48,f73,f100,f243,f427,f434,f439])).
% 0.20/0.43  fof(f439,plain,(
% 0.20/0.43    ~spl2_7 | spl2_17),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f435])).
% 0.20/0.43  fof(f435,plain,(
% 0.20/0.43    $false | (~spl2_7 | spl2_17)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f242,f433])).
% 0.20/0.43  fof(f433,plain,(
% 0.20/0.43    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | spl2_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f431])).
% 0.20/0.43  fof(f431,plain,(
% 0.20/0.43    spl2_17 <=> k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.43  fof(f242,plain,(
% 0.20/0.43    ( ! [X4] : (k2_xboole_0(X4,k1_xboole_0) = X4) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f241])).
% 0.20/0.44  fof(f241,plain,(
% 0.20/0.44    spl2_7 <=> ! [X4] : k2_xboole_0(X4,k1_xboole_0) = X4),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.44  fof(f434,plain,(
% 0.20/0.44    ~spl2_17 | spl2_16),
% 0.20/0.44    inference(avatar_split_clause,[],[f429,f424,f431])).
% 0.20/0.44  fof(f424,plain,(
% 0.20/0.44    spl2_16 <=> k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.44  fof(f429,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | spl2_16),
% 0.20/0.44    inference(forward_demodulation,[],[f428,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f19,f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.44  fof(f428,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k1_xboole_0) | spl2_16),
% 0.20/0.44    inference(forward_demodulation,[],[f426,f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f16,f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.44    inference(nnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.44  fof(f426,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) | spl2_16),
% 0.20/0.44    inference(avatar_component_clause,[],[f424])).
% 0.20/0.44  fof(f427,plain,(
% 0.20/0.44    ~spl2_16),
% 0.20/0.44    inference(avatar_split_clause,[],[f24,f424])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 0.20/0.44    inference(definition_unfolding,[],[f14,f20,f18])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    inference(negated_conjecture,[],[f8])).
% 0.20/0.44  fof(f8,conjecture,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.44  fof(f243,plain,(
% 0.20/0.44    spl2_7 | ~spl2_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f234,f98,f241])).
% 0.20/0.44  fof(f98,plain,(
% 0.20/0.44    spl2_5 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.44  fof(f234,plain,(
% 0.20/0.44    ( ! [X4] : (k2_xboole_0(X4,k1_xboole_0) = X4) ) | ~spl2_5),
% 0.20/0.44    inference(forward_demodulation,[],[f233,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.20/0.44    inference(definition_unfolding,[],[f15,f20])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.44  fof(f233,plain,(
% 0.20/0.44    ( ! [X4] : (k2_xboole_0(k4_xboole_0(X4,k1_xboole_0),k4_xboole_0(k1_xboole_0,X4)) = k2_xboole_0(X4,k1_xboole_0)) ) | ~spl2_5),
% 0.20/0.44    inference(forward_demodulation,[],[f222,f99])).
% 0.20/0.44  fof(f99,plain,(
% 0.20/0.44    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) ) | ~spl2_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f98])).
% 0.20/0.44  fof(f222,plain,(
% 0.20/0.44    ( ! [X4,X5] : (k2_xboole_0(X4,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(k1_xboole_0,X5)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X5),X4))) )),
% 0.20/0.44    inference(superposition,[],[f23,f75])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.20/0.44    inference(superposition,[],[f68,f68])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 0.20/0.44    inference(forward_demodulation,[],[f64,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(superposition,[],[f27,f27])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) )),
% 0.20/0.44    inference(superposition,[],[f25,f27])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f17,f20])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    spl2_5 | ~spl2_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f76,f70,f98])).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    spl2_3 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) ) | ~spl2_3),
% 0.20/0.44    inference(superposition,[],[f68,f72])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f70])).
% 0.20/0.44  fof(f73,plain,(
% 0.20/0.44    spl2_3 | ~spl2_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f65,f45,f70])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    spl2_2 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 0.20/0.44    inference(superposition,[],[f25,f47])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f45])).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    spl2_2 | ~spl2_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f42,f38,f45])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    spl2_1 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_1),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f40,f22])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl2_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f38])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    spl2_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f36,f38])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.44    inference(superposition,[],[f32,f27])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X2,X3] : (r1_tarski(k1_xboole_0,k4_xboole_0(X2,X3))) )),
% 0.20/0.44    inference(superposition,[],[f16,f27])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (27555)------------------------------
% 0.20/0.44  % (27555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (27555)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (27555)Memory used [KB]: 10746
% 0.20/0.44  % (27555)Time elapsed: 0.034 s
% 0.20/0.44  % (27555)------------------------------
% 0.20/0.44  % (27555)------------------------------
% 0.20/0.44  % (27537)Success in time 0.082 s
%------------------------------------------------------------------------------
