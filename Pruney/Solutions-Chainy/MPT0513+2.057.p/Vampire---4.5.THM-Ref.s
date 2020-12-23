%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :  126 ( 164 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f48,f52,f56,f64,f71,f79,f82])).

fof(f82,plain,
    ( spl1_1
    | ~ spl1_11 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl1_1
    | ~ spl1_11 ),
    inference(trivial_inequality_removal,[],[f80])).

fof(f80,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_11 ),
    inference(superposition,[],[f27,f78])).

fof(f78,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl1_11
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f27,plain,
    ( k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl1_1
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f79,plain,
    ( spl1_11
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_9
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f75,f68,f62,f50,f45,f77])).

fof(f45,plain,
    ( spl1_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f50,plain,
    ( spl1_6
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f62,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f68,plain,
    ( spl1_10
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f75,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_9
    | ~ spl1_10 ),
    inference(subsumption_resolution,[],[f74,f70])).

fof(f70,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f74,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f73,f51])).

fof(f51,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(superposition,[],[f63,f47])).

fof(f47,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f71,plain,
    ( spl1_10
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f66,f54,f35,f30,f68])).

fof(f30,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f35,plain,
    ( spl1_3
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f54,plain,
    ( spl1_7
  <=> ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f66,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f65,f32])).

fof(f32,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f65,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(superposition,[],[f55,f37])).

fof(f37,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f55,plain,
    ( ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f64,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f56,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f52,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f48,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f38,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

fof(f33,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f28,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n021.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:14:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (9578)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (9577)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (9581)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (9577)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f28,f33,f38,f48,f52,f56,f64,f71,f79,f82])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl1_1 | ~spl1_11),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f81])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    $false | (spl1_1 | ~spl1_11)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f80])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_11)),
% 0.21/0.43    inference(superposition,[],[f27,f78])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl1_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f77])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    spl1_11 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    spl1_1 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    spl1_11 | ~spl1_5 | ~spl1_6 | ~spl1_9 | ~spl1_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f75,f68,f62,f50,f45,f77])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl1_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl1_6 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl1_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl1_10 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl1_5 | ~spl1_6 | ~spl1_9 | ~spl1_10)),
% 0.21/0.43    inference(subsumption_resolution,[],[f74,f70])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | ~spl1_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f68])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_5 | ~spl1_6 | ~spl1_9)),
% 0.21/0.43    inference(subsumption_resolution,[],[f73,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f50])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_5 | ~spl1_9)),
% 0.21/0.43    inference(superposition,[],[f63,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f45])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl1_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f62])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl1_10 | ~spl1_2 | ~spl1_3 | ~spl1_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f66,f54,f35,f30,f68])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    spl1_3 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl1_7 <=> ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_3 | ~spl1_7)),
% 0.21/0.43    inference(subsumption_resolution,[],[f65,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f30])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | (~spl1_3 | ~spl1_7)),
% 0.21/0.43    inference(superposition,[],[f55,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f35])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl1_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl1_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f62])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl1_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f54])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl1_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f50])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl1_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f45])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl1_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f35])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ~spl1_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f15,f25])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (9577)------------------------------
% 0.21/0.43  % (9577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (9577)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (9577)Memory used [KB]: 10490
% 0.21/0.43  % (9577)Time elapsed: 0.009 s
% 0.21/0.43  % (9577)------------------------------
% 0.21/0.43  % (9577)------------------------------
% 0.21/0.44  % (9571)Success in time 0.078 s
%------------------------------------------------------------------------------
