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
% DateTime   : Thu Dec  3 12:48:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  79 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :  141 ( 189 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f44,f48,f52,f56,f64,f69,f75,f82,f87])).

fof(f87,plain,
    ( spl1_1
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | spl1_1
    | ~ spl1_12 ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_12 ),
    inference(superposition,[],[f28,f81])).

fof(f81,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl1_12
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f28,plain,
    ( k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl1_1
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f82,plain,
    ( spl1_12
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_10
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f78,f73,f67,f41,f31,f80])).

fof(f31,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f41,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f67,plain,
    ( spl1_10
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f73,plain,
    ( spl1_11
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(k1_relat_1(X0),X1)
        | k1_xboole_0 = k7_relat_1(X0,X1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f78,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_10
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f77,f68])).

fof(f68,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f76,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f76,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | ~ r1_xboole_0(k1_relat_1(k1_xboole_0),X0) )
    | ~ spl1_2
    | ~ spl1_11 ),
    inference(resolution,[],[f74,f33])).

fof(f33,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(X0,X1)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f75,plain,
    ( spl1_11
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f71,f54,f50,f73])).

fof(f50,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f54,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_relat_1(X0),X1)
        | k1_xboole_0 = k7_relat_1(X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(resolution,[],[f55,f51])).

fof(f51,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f69,plain,
    ( spl1_10
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f65,f62,f46,f67])).

fof(f46,plain,
    ( spl1_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f62,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f65,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl1_5
    | ~ spl1_9 ),
    inference(resolution,[],[f63,f47])).

fof(f47,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f24,f62])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f56,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f52,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f48,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f44,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f34,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f29,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f16,f26])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:00:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (11005)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (11004)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (11004)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f29,f34,f44,f48,f52,f56,f64,f69,f75,f82,f87])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl1_1 | ~spl1_12),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f86])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    $false | (spl1_1 | ~spl1_12)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f83])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_12)),
% 0.21/0.42    inference(superposition,[],[f28,f81])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl1_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f80])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl1_12 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    spl1_1 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl1_12 | ~spl1_2 | ~spl1_4 | ~spl1_10 | ~spl1_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f78,f73,f67,f41,f31,f80])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl1_10 <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl1_11 <=> ! [X1,X0] : (~r1_xboole_0(k1_relat_1(X0),X1) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl1_2 | ~spl1_4 | ~spl1_10 | ~spl1_11)),
% 0.21/0.43    inference(subsumption_resolution,[],[f77,f68])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl1_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f67])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl1_2 | ~spl1_4 | ~spl1_11)),
% 0.21/0.43    inference(forward_demodulation,[],[f76,f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f41])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~r1_xboole_0(k1_relat_1(k1_xboole_0),X0)) ) | (~spl1_2 | ~spl1_11)),
% 0.21/0.43    inference(resolution,[],[f74,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(k1_relat_1(X0),X1)) ) | ~spl1_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f73])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl1_11 | ~spl1_6 | ~spl1_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f71,f54,f50,f73])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl1_6 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl1_7 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X0),X1) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_xboole_0(X0)) ) | (~spl1_6 | ~spl1_7)),
% 0.21/0.43    inference(resolution,[],[f55,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f50])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) ) | ~spl1_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl1_10 | ~spl1_5 | ~spl1_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f65,f62,f46,f67])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl1_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl1_9 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | (~spl1_5 | ~spl1_9)),
% 0.21/0.43    inference(resolution,[],[f63,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl1_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f46])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl1_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f62])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    spl1_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f62])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl1_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f54])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(nnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl1_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl1_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f46])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl1_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f41])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f31])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ~spl1_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f26])).
% 0.21/0.43  fof(f16,plain,(
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
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (11004)------------------------------
% 0.21/0.43  % (11004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (11004)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (11004)Memory used [KB]: 10618
% 0.21/0.43  % (11004)Time elapsed: 0.006 s
% 0.21/0.43  % (11004)------------------------------
% 0.21/0.43  % (11004)------------------------------
% 0.21/0.43  % (11003)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (10998)Success in time 0.072 s
%------------------------------------------------------------------------------
