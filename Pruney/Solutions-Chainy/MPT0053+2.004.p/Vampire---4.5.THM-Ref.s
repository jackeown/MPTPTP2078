%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:56 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  60 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   87 ( 117 expanded)
%              Number of equality atoms :   33 (  45 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f41,f46,f112,f134,f175])).

fof(f175,plain,
    ( spl2_1
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl2_1
    | ~ spl2_19 ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_1
    | ~ spl2_19 ),
    inference(superposition,[],[f20,f132])).

fof(f132,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,X0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl2_19
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f20,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f134,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f122,f109,f27,f131])).

fof(f27,plain,
    ( spl2_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f109,plain,
    ( spl2_16
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f122,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X2))
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(superposition,[],[f110,f28])).

fof(f28,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f110,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f112,plain,
    ( spl2_16
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f85,f44,f39,f109])).

fof(f39,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f44,plain,
    ( spl2_7
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f85,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(superposition,[],[f45,f40])).

fof(f40,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f39])).

fof(f45,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f44])).

fof(f46,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f42,f31,f23,f44])).

fof(f23,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f31,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f42,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f32,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f41,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f33,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f29,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f12,f23])).

fof(f12,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (25545)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.42  % (25545)Refutation found. Thanks to Tanya!
% 0.14/0.42  % SZS status Theorem for theBenchmark
% 0.14/0.42  % SZS output start Proof for theBenchmark
% 0.14/0.42  fof(f177,plain,(
% 0.14/0.42    $false),
% 0.14/0.42    inference(avatar_sat_refutation,[],[f21,f25,f29,f33,f41,f46,f112,f134,f175])).
% 0.14/0.42  fof(f175,plain,(
% 0.14/0.42    spl2_1 | ~spl2_19),
% 0.14/0.42    inference(avatar_contradiction_clause,[],[f174])).
% 0.14/0.42  fof(f174,plain,(
% 0.14/0.42    $false | (spl2_1 | ~spl2_19)),
% 0.14/0.42    inference(trivial_inequality_removal,[],[f173])).
% 0.14/0.42  fof(f173,plain,(
% 0.14/0.42    k1_xboole_0 != k1_xboole_0 | (spl2_1 | ~spl2_19)),
% 0.14/0.42    inference(superposition,[],[f20,f132])).
% 0.14/0.42  fof(f132,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,X0))) ) | ~spl2_19),
% 0.14/0.42    inference(avatar_component_clause,[],[f131])).
% 0.14/0.42  fof(f131,plain,(
% 0.14/0.42    spl2_19 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,X0))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.14/0.42  fof(f20,plain,(
% 0.14/0.42    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | spl2_1),
% 0.14/0.42    inference(avatar_component_clause,[],[f18])).
% 0.14/0.42  fof(f18,plain,(
% 0.14/0.42    spl2_1 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.14/0.42  fof(f134,plain,(
% 0.14/0.42    spl2_19 | ~spl2_3 | ~spl2_16),
% 0.14/0.42    inference(avatar_split_clause,[],[f122,f109,f27,f131])).
% 0.14/0.42  fof(f27,plain,(
% 0.14/0.42    spl2_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.14/0.43  fof(f109,plain,(
% 0.14/0.43    spl2_16 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.14/0.43  fof(f122,plain,(
% 0.14/0.43    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X2))) ) | (~spl2_3 | ~spl2_16)),
% 0.14/0.43    inference(superposition,[],[f110,f28])).
% 0.14/0.43  fof(f28,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_3),
% 0.14/0.43    inference(avatar_component_clause,[],[f27])).
% 0.14/0.43  fof(f110,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) ) | ~spl2_16),
% 0.14/0.43    inference(avatar_component_clause,[],[f109])).
% 0.14/0.43  fof(f112,plain,(
% 0.14/0.43    spl2_16 | ~spl2_6 | ~spl2_7),
% 0.14/0.43    inference(avatar_split_clause,[],[f85,f44,f39,f109])).
% 0.14/0.43  fof(f39,plain,(
% 0.14/0.43    spl2_6 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.14/0.43  fof(f44,plain,(
% 0.14/0.43    spl2_7 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.14/0.43  fof(f85,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) ) | (~spl2_6 | ~spl2_7)),
% 0.14/0.43    inference(superposition,[],[f45,f40])).
% 0.14/0.43  fof(f40,plain,(
% 0.14/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_6),
% 0.14/0.43    inference(avatar_component_clause,[],[f39])).
% 0.14/0.43  fof(f45,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl2_7),
% 0.14/0.43    inference(avatar_component_clause,[],[f44])).
% 0.14/0.43  fof(f46,plain,(
% 0.14/0.43    spl2_7 | ~spl2_2 | ~spl2_4),
% 0.14/0.43    inference(avatar_split_clause,[],[f42,f31,f23,f44])).
% 0.14/0.43  fof(f23,plain,(
% 0.14/0.43    spl2_2 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.14/0.43  fof(f31,plain,(
% 0.14/0.43    spl2_4 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.14/0.43  fof(f42,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl2_2 | ~spl2_4)),
% 0.14/0.43    inference(resolution,[],[f32,f24])).
% 0.14/0.43  fof(f24,plain,(
% 0.14/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_2),
% 0.14/0.43    inference(avatar_component_clause,[],[f23])).
% 0.14/0.43  fof(f32,plain,(
% 0.14/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_4),
% 0.14/0.43    inference(avatar_component_clause,[],[f31])).
% 0.14/0.43  fof(f41,plain,(
% 0.14/0.43    spl2_6),
% 0.14/0.43    inference(avatar_split_clause,[],[f16,f39])).
% 0.14/0.43  fof(f16,plain,(
% 0.14/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.14/0.43    inference(cnf_transformation,[],[f4])).
% 0.14/0.43  fof(f4,axiom,(
% 0.14/0.43    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.14/0.43  fof(f33,plain,(
% 0.14/0.43    spl2_4),
% 0.14/0.43    inference(avatar_split_clause,[],[f15,f31])).
% 0.14/0.43  fof(f15,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f10])).
% 0.14/0.43  fof(f10,plain,(
% 0.14/0.43    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.14/0.43    inference(nnf_transformation,[],[f2])).
% 0.14/0.43  fof(f2,axiom,(
% 0.14/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.14/0.43  fof(f29,plain,(
% 0.14/0.43    spl2_3),
% 0.14/0.43    inference(avatar_split_clause,[],[f13,f27])).
% 0.14/0.43  fof(f13,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f1])).
% 0.14/0.43  fof(f1,axiom,(
% 0.14/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.14/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.14/0.43  fof(f25,plain,(
% 0.14/0.43    spl2_2),
% 0.14/0.43    inference(avatar_split_clause,[],[f12,f23])).
% 0.14/0.43  fof(f12,plain,(
% 0.14/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ~spl2_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f11,f18])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) => k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (25545)------------------------------
% 0.22/0.43  % (25545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (25545)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (25545)Memory used [KB]: 10618
% 0.22/0.43  % (25545)Time elapsed: 0.010 s
% 0.22/0.43  % (25545)------------------------------
% 0.22/0.43  % (25545)------------------------------
% 0.22/0.43  % (25539)Success in time 0.07 s
%------------------------------------------------------------------------------
