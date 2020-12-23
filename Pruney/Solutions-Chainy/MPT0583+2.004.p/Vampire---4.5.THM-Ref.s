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
% DateTime   : Thu Dec  3 12:50:51 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 113 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :    6
%              Number of atoms          :  199 ( 312 expanded)
%              Number of equality atoms :   60 (  94 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f50,f54,f58,f62,f70,f76,f89,f99,f108,f130,f134])).

fof(f134,plain,
    ( spl2_1
    | ~ spl2_13
    | ~ spl2_20 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl2_1
    | ~ spl2_13
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f132,f31])).

fof(f31,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_1
  <=> k1_xboole_0 = k7_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f132,plain,
    ( k1_xboole_0 = k7_relat_1(sK0,sK1)
    | ~ spl2_13
    | ~ spl2_20 ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK0,sK1)
    | ~ spl2_13
    | ~ spl2_20 ),
    inference(superposition,[],[f129,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_13
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f129,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl2_20
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK0,X0)
        | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f130,plain,
    ( spl2_20
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f126,f106,f52,f39,f128])).

fof(f39,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f52,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f106,plain,
    ( spl2_16
  <=> ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0)
        | ~ v1_relat_1(k7_relat_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f126,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK0,X0)
        | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0) )
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f41,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f125,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK0,X0)
        | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(resolution,[],[f107,f53])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k7_relat_1(sK0,X0))
        | k1_xboole_0 = k7_relat_1(sK0,X0)
        | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f104,f97,f48,f106])).

fof(f48,plain,
    ( spl2_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f97,plain,
    ( spl2_14
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f104,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0)
        | ~ v1_relat_1(k7_relat_1(sK0,X0)) )
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(superposition,[],[f49,f98])).

fof(f98,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f49,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f99,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f94,f56,f39,f97])).

fof(f56,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f94,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f57,f41])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f89,plain,
    ( spl2_13
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f79,f73,f68,f86])).

fof(f68,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f73,plain,
    ( spl2_11
  <=> r1_xboole_0(k1_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f79,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(resolution,[],[f69,f75])).

fof(f75,plain,
    ( r1_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f76,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f71,f60,f34,f73])).

fof(f34,plain,
    ( spl2_2
  <=> r1_xboole_0(sK1,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f60,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f71,plain,
    ( r1_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(resolution,[],[f61,f36])).

fof(f36,plain,
    ( r1_xboole_0(sK1,k1_relat_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f70,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f62,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f58,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f54,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f50,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f42,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,sK1)
    & r1_xboole_0(sK1,k1_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k7_relat_1(X0,X1)
            & r1_xboole_0(X1,k1_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(sK0,X1)
          & r1_xboole_0(X1,k1_relat_1(sK0)) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( k1_xboole_0 != k7_relat_1(sK0,X1)
        & r1_xboole_0(X1,k1_relat_1(sK0)) )
   => ( k1_xboole_0 != k7_relat_1(sK0,sK1)
      & r1_xboole_0(sK1,k1_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(X0,X1)
          & r1_xboole_0(X1,k1_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r1_xboole_0(X1,k1_relat_1(X0))
           => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    r1_xboole_0(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f29])).

fof(f20,plain,(
    k1_xboole_0 != k7_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:19:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (13471)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.42  % (13472)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.14/0.42  % (13473)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.14/0.42  % (13471)Refutation found. Thanks to Tanya!
% 0.14/0.42  % SZS status Theorem for theBenchmark
% 0.14/0.42  % SZS output start Proof for theBenchmark
% 0.14/0.42  fof(f135,plain,(
% 0.14/0.42    $false),
% 0.14/0.42    inference(avatar_sat_refutation,[],[f32,f37,f42,f50,f54,f58,f62,f70,f76,f89,f99,f108,f130,f134])).
% 0.14/0.42  fof(f134,plain,(
% 0.14/0.42    spl2_1 | ~spl2_13 | ~spl2_20),
% 0.14/0.42    inference(avatar_contradiction_clause,[],[f133])).
% 0.14/0.42  fof(f133,plain,(
% 0.14/0.42    $false | (spl2_1 | ~spl2_13 | ~spl2_20)),
% 0.14/0.42    inference(subsumption_resolution,[],[f132,f31])).
% 0.14/0.42  fof(f31,plain,(
% 0.14/0.42    k1_xboole_0 != k7_relat_1(sK0,sK1) | spl2_1),
% 0.14/0.42    inference(avatar_component_clause,[],[f29])).
% 0.14/0.42  fof(f29,plain,(
% 0.14/0.42    spl2_1 <=> k1_xboole_0 = k7_relat_1(sK0,sK1)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.14/0.42  fof(f132,plain,(
% 0.14/0.42    k1_xboole_0 = k7_relat_1(sK0,sK1) | (~spl2_13 | ~spl2_20)),
% 0.14/0.42    inference(trivial_inequality_removal,[],[f131])).
% 0.14/0.42  fof(f131,plain,(
% 0.14/0.42    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK0,sK1) | (~spl2_13 | ~spl2_20)),
% 0.14/0.42    inference(superposition,[],[f129,f88])).
% 0.14/0.42  fof(f88,plain,(
% 0.14/0.42    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),sK1) | ~spl2_13),
% 0.14/0.42    inference(avatar_component_clause,[],[f86])).
% 0.14/0.42  fof(f86,plain,(
% 0.14/0.42    spl2_13 <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),sK1)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.14/0.42  fof(f129,plain,(
% 0.14/0.42    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0)) ) | ~spl2_20),
% 0.14/0.42    inference(avatar_component_clause,[],[f128])).
% 0.14/0.42  fof(f128,plain,(
% 0.14/0.42    spl2_20 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(sK0,X0) | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.14/0.42  fof(f130,plain,(
% 0.14/0.42    spl2_20 | ~spl2_3 | ~spl2_6 | ~spl2_16),
% 0.14/0.42    inference(avatar_split_clause,[],[f126,f106,f52,f39,f128])).
% 0.14/0.42  fof(f39,plain,(
% 0.14/0.42    spl2_3 <=> v1_relat_1(sK0)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.14/0.42  fof(f52,plain,(
% 0.14/0.42    spl2_6 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.14/0.42  fof(f106,plain,(
% 0.14/0.42    spl2_16 <=> ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0) | ~v1_relat_1(k7_relat_1(sK0,X0)))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.14/0.42  fof(f126,plain,(
% 0.14/0.42    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK0,X0) | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0)) ) | (~spl2_3 | ~spl2_6 | ~spl2_16)),
% 0.14/0.42    inference(subsumption_resolution,[],[f125,f41])).
% 0.14/0.42  fof(f41,plain,(
% 0.14/0.42    v1_relat_1(sK0) | ~spl2_3),
% 0.14/0.42    inference(avatar_component_clause,[],[f39])).
% 0.14/0.42  fof(f125,plain,(
% 0.14/0.42    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK0,X0) | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0) | ~v1_relat_1(sK0)) ) | (~spl2_6 | ~spl2_16)),
% 0.14/0.42    inference(resolution,[],[f107,f53])).
% 0.14/0.42  fof(f53,plain,(
% 0.14/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.14/0.42    inference(avatar_component_clause,[],[f52])).
% 0.14/0.42  fof(f107,plain,(
% 0.14/0.42    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK0,X0)) | k1_xboole_0 = k7_relat_1(sK0,X0) | k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0)) ) | ~spl2_16),
% 0.14/0.42    inference(avatar_component_clause,[],[f106])).
% 0.14/0.42  fof(f108,plain,(
% 0.14/0.42    spl2_16 | ~spl2_5 | ~spl2_14),
% 0.14/0.42    inference(avatar_split_clause,[],[f104,f97,f48,f106])).
% 0.14/0.42  fof(f48,plain,(
% 0.14/0.42    spl2_5 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.14/0.42  fof(f97,plain,(
% 0.14/0.42    spl2_14 <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.14/0.42  fof(f104,plain,(
% 0.14/0.42    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_relat_1(sK0),X0) | k1_xboole_0 = k7_relat_1(sK0,X0) | ~v1_relat_1(k7_relat_1(sK0,X0))) ) | (~spl2_5 | ~spl2_14)),
% 0.14/0.42    inference(superposition,[],[f49,f98])).
% 0.14/0.42  fof(f98,plain,(
% 0.14/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)) ) | ~spl2_14),
% 0.14/0.42    inference(avatar_component_clause,[],[f97])).
% 0.14/0.42  fof(f49,plain,(
% 0.14/0.42    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.14/0.42    inference(avatar_component_clause,[],[f48])).
% 0.14/0.42  fof(f99,plain,(
% 0.14/0.42    spl2_14 | ~spl2_3 | ~spl2_7),
% 0.14/0.42    inference(avatar_split_clause,[],[f94,f56,f39,f97])).
% 0.14/0.42  fof(f56,plain,(
% 0.14/0.42    spl2_7 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.14/0.42  fof(f94,plain,(
% 0.14/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)) ) | (~spl2_3 | ~spl2_7)),
% 0.14/0.42    inference(resolution,[],[f57,f41])).
% 0.14/0.42  fof(f57,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) ) | ~spl2_7),
% 0.14/0.42    inference(avatar_component_clause,[],[f56])).
% 0.14/0.42  fof(f89,plain,(
% 0.14/0.42    spl2_13 | ~spl2_10 | ~spl2_11),
% 0.14/0.42    inference(avatar_split_clause,[],[f79,f73,f68,f86])).
% 0.14/0.42  fof(f68,plain,(
% 0.14/0.42    spl2_10 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.14/0.42  fof(f73,plain,(
% 0.14/0.42    spl2_11 <=> r1_xboole_0(k1_relat_1(sK0),sK1)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.14/0.42  fof(f79,plain,(
% 0.14/0.42    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),sK1) | (~spl2_10 | ~spl2_11)),
% 0.14/0.42    inference(resolution,[],[f69,f75])).
% 0.14/0.42  fof(f75,plain,(
% 0.14/0.42    r1_xboole_0(k1_relat_1(sK0),sK1) | ~spl2_11),
% 0.14/0.42    inference(avatar_component_clause,[],[f73])).
% 0.14/0.42  fof(f69,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl2_10),
% 0.14/0.42    inference(avatar_component_clause,[],[f68])).
% 0.14/0.42  fof(f76,plain,(
% 0.14/0.42    spl2_11 | ~spl2_2 | ~spl2_8),
% 0.14/0.42    inference(avatar_split_clause,[],[f71,f60,f34,f73])).
% 0.14/0.42  fof(f34,plain,(
% 0.14/0.42    spl2_2 <=> r1_xboole_0(sK1,k1_relat_1(sK0))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.14/0.42  fof(f60,plain,(
% 0.14/0.42    spl2_8 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.14/0.42  fof(f71,plain,(
% 0.14/0.42    r1_xboole_0(k1_relat_1(sK0),sK1) | (~spl2_2 | ~spl2_8)),
% 0.14/0.42    inference(resolution,[],[f61,f36])).
% 0.14/0.42  fof(f36,plain,(
% 0.14/0.42    r1_xboole_0(sK1,k1_relat_1(sK0)) | ~spl2_2),
% 0.14/0.42    inference(avatar_component_clause,[],[f34])).
% 0.14/0.42  fof(f61,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl2_8),
% 0.14/0.42    inference(avatar_component_clause,[],[f60])).
% 0.14/0.42  fof(f70,plain,(
% 0.14/0.42    spl2_10),
% 0.14/0.42    inference(avatar_split_clause,[],[f26,f68])).
% 0.14/0.42  fof(f26,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f17])).
% 0.14/0.42  fof(f17,plain,(
% 0.14/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.14/0.42    inference(nnf_transformation,[],[f1])).
% 0.14/0.42  fof(f1,axiom,(
% 0.14/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.14/0.42  fof(f62,plain,(
% 0.14/0.42    spl2_8),
% 0.14/0.42    inference(avatar_split_clause,[],[f25,f60])).
% 0.14/0.42  fof(f25,plain,(
% 0.14/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f13])).
% 0.14/0.42  fof(f13,plain,(
% 0.14/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f2])).
% 0.14/0.42  fof(f2,axiom,(
% 0.14/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.14/0.42  fof(f58,plain,(
% 0.14/0.42    spl2_7),
% 0.14/0.42    inference(avatar_split_clause,[],[f24,f56])).
% 0.14/0.42  fof(f24,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f12])).
% 0.14/0.42  fof(f12,plain,(
% 0.14/0.42    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f5])).
% 0.14/0.42  fof(f5,axiom,(
% 0.14/0.42    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.14/0.42  fof(f54,plain,(
% 0.14/0.42    spl2_6),
% 0.14/0.42    inference(avatar_split_clause,[],[f23,f52])).
% 0.14/0.42  fof(f23,plain,(
% 0.14/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f11])).
% 0.14/0.42  fof(f11,plain,(
% 0.14/0.42    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.14/0.42    inference(ennf_transformation,[],[f3])).
% 0.14/0.42  fof(f3,axiom,(
% 0.14/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.14/0.42  fof(f50,plain,(
% 0.14/0.42    spl2_5),
% 0.14/0.42    inference(avatar_split_clause,[],[f21,f48])).
% 0.14/0.42  fof(f21,plain,(
% 0.14/0.42    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f10])).
% 0.14/0.42  fof(f10,plain,(
% 0.14/0.42    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.14/0.42    inference(flattening,[],[f9])).
% 0.14/0.42  fof(f9,plain,(
% 0.14/0.42    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.14/0.42    inference(ennf_transformation,[],[f4])).
% 0.14/0.42  fof(f4,axiom,(
% 0.14/0.42    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.14/0.42  fof(f42,plain,(
% 0.14/0.42    spl2_3),
% 0.14/0.42    inference(avatar_split_clause,[],[f18,f39])).
% 0.14/0.42  fof(f18,plain,(
% 0.14/0.42    v1_relat_1(sK0)),
% 0.14/0.42    inference(cnf_transformation,[],[f16])).
% 0.14/0.42  fof(f16,plain,(
% 0.14/0.42    (k1_xboole_0 != k7_relat_1(sK0,sK1) & r1_xboole_0(sK1,k1_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.14/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15,f14])).
% 0.14/0.42  fof(f14,plain,(
% 0.14/0.42    ? [X0] : (? [X1] : (k1_xboole_0 != k7_relat_1(X0,X1) & r1_xboole_0(X1,k1_relat_1(X0))) & v1_relat_1(X0)) => (? [X1] : (k1_xboole_0 != k7_relat_1(sK0,X1) & r1_xboole_0(X1,k1_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.14/0.42    introduced(choice_axiom,[])).
% 0.14/0.42  fof(f15,plain,(
% 0.14/0.42    ? [X1] : (k1_xboole_0 != k7_relat_1(sK0,X1) & r1_xboole_0(X1,k1_relat_1(sK0))) => (k1_xboole_0 != k7_relat_1(sK0,sK1) & r1_xboole_0(sK1,k1_relat_1(sK0)))),
% 0.14/0.42    introduced(choice_axiom,[])).
% 0.14/0.42  fof(f8,plain,(
% 0.14/0.42    ? [X0] : (? [X1] : (k1_xboole_0 != k7_relat_1(X0,X1) & r1_xboole_0(X1,k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.14/0.42    inference(ennf_transformation,[],[f7])).
% 0.14/0.42  fof(f7,negated_conjecture,(
% 0.14/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.14/0.42    inference(negated_conjecture,[],[f6])).
% 0.14/0.42  fof(f6,conjecture,(
% 0.14/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.14/0.42  fof(f37,plain,(
% 0.14/0.42    spl2_2),
% 0.14/0.42    inference(avatar_split_clause,[],[f19,f34])).
% 0.14/0.42  fof(f19,plain,(
% 0.14/0.42    r1_xboole_0(sK1,k1_relat_1(sK0))),
% 0.14/0.42    inference(cnf_transformation,[],[f16])).
% 0.14/0.42  fof(f32,plain,(
% 0.14/0.42    ~spl2_1),
% 0.14/0.42    inference(avatar_split_clause,[],[f20,f29])).
% 0.14/0.42  fof(f20,plain,(
% 0.14/0.42    k1_xboole_0 != k7_relat_1(sK0,sK1)),
% 0.14/0.42    inference(cnf_transformation,[],[f16])).
% 0.14/0.42  % SZS output end Proof for theBenchmark
% 0.14/0.43  % (13471)------------------------------
% 0.14/0.43  % (13471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.43  % (13471)Termination reason: Refutation
% 0.14/0.43  
% 0.14/0.43  % (13471)Memory used [KB]: 10618
% 0.14/0.43  % (13471)Time elapsed: 0.008 s
% 0.14/0.43  % (13471)------------------------------
% 0.14/0.43  % (13471)------------------------------
% 0.14/0.43  % (13462)Success in time 0.065 s
%------------------------------------------------------------------------------
