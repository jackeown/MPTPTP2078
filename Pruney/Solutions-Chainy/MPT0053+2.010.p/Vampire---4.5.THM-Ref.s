%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  60 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   87 ( 117 expanded)
%              Number of equality atoms :   27 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f37,f48,f56,f80,f89])).

fof(f89,plain,
    ( spl2_1
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl2_1
    | ~ spl2_13 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_1
    | ~ spl2_13 ),
    inference(superposition,[],[f20,f79])).

fof(f79,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_13
  <=> ! [X5,X6] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f20,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f80,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f64,f54,f35,f78])).

fof(f35,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f54,plain,
    ( spl2_8
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f64,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f36,f55])).

fof(f55,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f56,plain,
    ( spl2_8
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f51,f45,f31,f54])).

fof(f31,plain,
    ( spl2_4
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f45,plain,
    ( spl2_7
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f51,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f46,f32])).

fof(f32,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f46,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f45])).

fof(f48,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f43,f27,f23,f45])).

fof(f23,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f27,plain,
    ( spl2_3
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f43,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f24,f28])).

fof(f28,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f24,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f37,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f33,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f29,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f25,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f21,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))
   => k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (24849)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.44  % (24851)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.45  % (24849)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f37,f48,f56,f80,f89])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    spl2_1 | ~spl2_13),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    $false | (spl2_1 | ~spl2_13)),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f87])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    k1_xboole_0 != k1_xboole_0 | (spl2_1 | ~spl2_13)),
% 0.20/0.45    inference(superposition,[],[f20,f79])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) ) | ~spl2_13),
% 0.20/0.45    inference(avatar_component_clause,[],[f78])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    spl2_13 <=> ! [X5,X6] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | spl2_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    spl2_1 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    spl2_13 | ~spl2_5 | ~spl2_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f64,f54,f35,f78])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    spl2_5 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    spl2_8 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) ) | (~spl2_5 | ~spl2_8)),
% 0.20/0.45    inference(resolution,[],[f36,f55])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f54])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f35])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    spl2_8 | ~spl2_4 | ~spl2_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f51,f45,f31,f54])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    spl2_4 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    spl2_7 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | (~spl2_4 | ~spl2_7)),
% 0.20/0.45    inference(superposition,[],[f46,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | ~spl2_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f31])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | ~spl2_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f45])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    spl2_7 | ~spl2_2 | ~spl2_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f43,f27,f23,f45])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    spl2_2 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    spl2_3 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl2_2 | ~spl2_3)),
% 0.20/0.45    inference(superposition,[],[f24,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f27])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f23])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    spl2_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f16,f35])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.45    inference(nnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    spl2_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f14,f31])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    spl2_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f13,f27])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    spl2_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f12,f23])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ~spl2_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f11,f18])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) => k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.45    inference(negated_conjecture,[],[f5])).
% 0.20/0.45  fof(f5,conjecture,(
% 0.20/0.45    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (24849)------------------------------
% 0.20/0.45  % (24849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (24849)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (24849)Memory used [KB]: 10618
% 0.20/0.45  % (24849)Time elapsed: 0.005 s
% 0.20/0.45  % (24849)------------------------------
% 0.20/0.45  % (24849)------------------------------
% 0.20/0.45  % (24843)Success in time 0.089 s
%------------------------------------------------------------------------------
