%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  82 expanded)
%              Number of leaves         :   16 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :  129 ( 187 expanded)
%              Number of equality atoms :   34 (  57 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f34,f38,f42,f54,f66,f76,f81,f87])).

fof(f87,plain,
    ( ~ spl1_4
    | ~ spl1_5
    | ~ spl1_7
    | spl1_10
    | ~ spl1_11 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_7
    | spl1_10
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f75,f85])).

fof(f85,plain,
    ( ! [X1] : r1_xboole_0(X1,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f83,f84])).

fof(f84,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f82,f37])).

fof(f37,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl1_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f82,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(superposition,[],[f53,f80])).

fof(f80,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl1_11
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f53,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl1_7
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f83,plain,
    ( ! [X1] : r1_xboole_0(k3_xboole_0(X1,X1),k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_11 ),
    inference(superposition,[],[f41,f80])).

fof(f41,plain,
    ( ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl1_5
  <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f75,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK0),k1_xboole_0)
    | spl1_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl1_10
  <=> r1_xboole_0(k1_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f81,plain,
    ( spl1_11
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f58,f52,f36,f32,f79])).

fof(f32,plain,
    ( spl1_3
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f58,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f55,f33])).

fof(f33,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f55,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(superposition,[],[f53,f37])).

fof(f76,plain,
    ( ~ spl1_10
    | ~ spl1_1
    | spl1_2
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f67,f64,f27,f22,f73])).

fof(f22,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f27,plain,
    ( spl1_2
  <=> k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f64,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f67,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK0),k1_xboole_0)
    | ~ spl1_1
    | spl1_2
    | ~ spl1_9 ),
    inference(unit_resulting_resolution,[],[f24,f29,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f29,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f24,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f66,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f20,f64])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

% (15105)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f54,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f18,f52])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

fof(f38,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f34,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f30,plain,(
    ~ spl1_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f25,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f13,f22])).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:15:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (15106)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (15097)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (15092)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (15097)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f25,f30,f34,f38,f42,f54,f66,f76,f81,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ~spl1_4 | ~spl1_5 | ~spl1_7 | spl1_10 | ~spl1_11),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    $false | (~spl1_4 | ~spl1_5 | ~spl1_7 | spl1_10 | ~spl1_11)),
% 0.21/0.47    inference(subsumption_resolution,[],[f75,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) ) | (~spl1_4 | ~spl1_5 | ~spl1_7 | ~spl1_11)),
% 0.21/0.47    inference(forward_demodulation,[],[f83,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | (~spl1_4 | ~spl1_7 | ~spl1_11)),
% 0.21/0.47    inference(forward_demodulation,[],[f82,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    spl1_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) ) | (~spl1_7 | ~spl1_11)),
% 0.21/0.47    inference(superposition,[],[f53,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl1_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl1_11 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl1_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl1_7 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X1] : (r1_xboole_0(k3_xboole_0(X1,X1),k1_xboole_0)) ) | (~spl1_5 | ~spl1_11)),
% 0.21/0.47    inference(superposition,[],[f41,f80])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | ~spl1_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl1_5 <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ~r1_xboole_0(k1_relat_1(sK0),k1_xboole_0) | spl1_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl1_10 <=> r1_xboole_0(k1_relat_1(sK0),k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl1_11 | ~spl1_3 | ~spl1_4 | ~spl1_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f58,f52,f36,f32,f79])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl1_3 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_7)),
% 0.21/0.47    inference(forward_demodulation,[],[f55,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl1_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f32])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl1_4 | ~spl1_7)),
% 0.21/0.47    inference(superposition,[],[f53,f37])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ~spl1_10 | ~spl1_1 | spl1_2 | ~spl1_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f67,f64,f27,f22,f73])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    spl1_1 <=> v1_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    spl1_2 <=> k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl1_9 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ~r1_xboole_0(k1_relat_1(sK0),k1_xboole_0) | (~spl1_1 | spl1_2 | ~spl1_9)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f24,f29,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl1_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) | spl1_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f27])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    v1_relat_1(sK0) | ~spl1_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f22])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl1_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f64])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  % (15105)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl1_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f52])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl1_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f17,f40])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl1_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f16,f36])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl1_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ~spl1_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f14,f27])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    spl1_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f13,f22])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (15097)------------------------------
% 0.21/0.47  % (15097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (15097)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (15097)Memory used [KB]: 6140
% 0.21/0.47  % (15097)Time elapsed: 0.053 s
% 0.21/0.47  % (15097)------------------------------
% 0.21/0.47  % (15097)------------------------------
% 0.21/0.47  % (15091)Success in time 0.11 s
%------------------------------------------------------------------------------
