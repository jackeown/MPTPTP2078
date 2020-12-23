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
% DateTime   : Thu Dec  3 12:48:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 107 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :    6
%              Number of atoms          :  174 ( 265 expanded)
%              Number of equality atoms :   33 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f36,f44,f48,f52,f56,f68,f79,f89,f101,f107,f115])).

fof(f115,plain,
    ( spl1_1
    | ~ spl1_16
    | ~ spl1_17 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl1_1
    | ~ spl1_16
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f113,f26])).

fof(f26,plain,
    ( sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl1_1
  <=> sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f113,plain,
    ( sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    | ~ spl1_16
    | ~ spl1_17 ),
    inference(resolution,[],[f106,f100])).

fof(f100,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl1_16
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | sK0 = k5_relat_1(sK0,k6_relat_1(X0)) )
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl1_17
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | sK0 = k5_relat_1(sK0,k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f107,plain,
    ( spl1_17
    | ~ spl1_2
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f102,f54,f29,f105])).

fof(f29,plain,
    ( spl1_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f54,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | sK0 = k5_relat_1(sK0,k6_relat_1(X0)) )
    | ~ spl1_2
    | ~ spl1_8 ),
    inference(resolution,[],[f55,f31])).

fof(f31,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f101,plain,
    ( spl1_16
    | ~ spl1_5
    | ~ spl1_10
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f97,f87,f66,f42,f99])).

fof(f42,plain,
    ( spl1_5
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f66,plain,
    ( spl1_10
  <=> ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f87,plain,
    ( spl1_14
  <=> ! [X1,X2] : r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f97,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl1_5
    | ~ spl1_10
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f96,f43])).

fof(f43,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f96,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k6_relat_1(X0)),X0)
    | ~ spl1_10
    | ~ spl1_14 ),
    inference(superposition,[],[f88,f67])).

fof(f67,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f88,plain,
    ( ! [X2,X1] : r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl1_14
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f81,f77,f34,f87])).

fof(f34,plain,
    ( spl1_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f77,plain,
    ( spl1_12
  <=> ! [X1,X2] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)),X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f81,plain,
    ( ! [X2,X1] : r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(resolution,[],[f78,f35])).

fof(f35,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f78,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)),X2) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f79,plain,
    ( spl1_12
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f75,f50,f42,f34,f77])).

fof(f50,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f75,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)),X2)
        | ~ v1_relat_1(X1) )
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f70,f43])).

fof(f70,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)),k1_relat_1(k6_relat_1(X2))) )
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(resolution,[],[f51,f35])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f68,plain,
    ( spl1_10
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f64,f46,f42,f34,f66])).

fof(f46,plain,
    ( spl1_6
  <=> ! [X0] :
        ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f64,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f58,f43])).

fof(f58,plain,
    ( ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0))
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(resolution,[],[f47,f35])).

fof(f47,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f56,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f52,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f48,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f44,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f36,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f32,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f27,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f16,f24])).

fof(f16,plain,(
    sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (11909)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (11909)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f27,f32,f36,f44,f48,f52,f56,f68,f79,f89,f101,f107,f115])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    spl1_1 | ~spl1_16 | ~spl1_17),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    $false | (spl1_1 | ~spl1_16 | ~spl1_17)),
% 0.21/0.42    inference(subsumption_resolution,[],[f113,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) | spl1_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    spl1_1 <=> sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    sK0 = k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) | (~spl1_16 | ~spl1_17)),
% 0.21/0.42    inference(resolution,[],[f106,f100])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl1_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f99])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    spl1_16 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | sK0 = k5_relat_1(sK0,k6_relat_1(X0))) ) | ~spl1_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f105])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    spl1_17 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | sK0 = k5_relat_1(sK0,k6_relat_1(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    spl1_17 | ~spl1_2 | ~spl1_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f102,f54,f29,f105])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    spl1_2 <=> v1_relat_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl1_8 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | sK0 = k5_relat_1(sK0,k6_relat_1(X0))) ) | (~spl1_2 | ~spl1_8)),
% 0.21/0.42    inference(resolution,[],[f55,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    v1_relat_1(sK0) | ~spl1_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f29])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) ) | ~spl1_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f54])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    spl1_16 | ~spl1_5 | ~spl1_10 | ~spl1_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f97,f87,f66,f42,f99])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl1_5 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl1_10 <=> ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl1_14 <=> ! [X1,X2] : r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl1_5 | ~spl1_10 | ~spl1_14)),
% 0.21/0.42    inference(forward_demodulation,[],[f96,f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl1_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),X0)) ) | (~spl1_10 | ~spl1_14)),
% 0.21/0.42    inference(superposition,[],[f88,f67])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) | ~spl1_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)) ) | ~spl1_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f87])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    spl1_14 | ~spl1_3 | ~spl1_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f81,f77,f34,f87])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl1_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    spl1_12 <=> ! [X1,X2] : (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)),X2) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),X1)) ) | (~spl1_3 | ~spl1_12)),
% 0.21/0.42    inference(resolution,[],[f78,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f34])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    ( ! [X2,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)),X2)) ) | ~spl1_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f77])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    spl1_12 | ~spl1_3 | ~spl1_5 | ~spl1_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f75,f50,f42,f34,f77])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl1_7 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)),X2) | ~v1_relat_1(X1)) ) | (~spl1_3 | ~spl1_5 | ~spl1_7)),
% 0.21/0.42    inference(forward_demodulation,[],[f70,f43])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    ( ! [X2,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X2),X1)),k1_relat_1(k6_relat_1(X2)))) ) | (~spl1_3 | ~spl1_7)),
% 0.21/0.42    inference(resolution,[],[f51,f35])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))) ) | ~spl1_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f50])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl1_10 | ~spl1_3 | ~spl1_5 | ~spl1_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f46,f42,f34,f66])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl1_6 <=> ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) | (~spl1_3 | ~spl1_5 | ~spl1_6)),
% 0.21/0.42    inference(forward_demodulation,[],[f58,f43])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0))) ) | (~spl1_3 | ~spl1_6)),
% 0.21/0.42    inference(resolution,[],[f47,f35])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) ) | ~spl1_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl1_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f54])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl1_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl1_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f46])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl1_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f42])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f34])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f29])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0 & v1_relat_1(X0)) => (sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) != X0 & v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ~spl1_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f24])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    sK0 != k5_relat_1(sK0,k6_relat_1(k2_relat_1(sK0)))),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (11909)------------------------------
% 0.21/0.42  % (11909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (11909)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (11909)Memory used [KB]: 10618
% 0.21/0.42  % (11909)Time elapsed: 0.007 s
% 0.21/0.42  % (11909)------------------------------
% 0.21/0.42  % (11909)------------------------------
% 0.21/0.42  % (11903)Success in time 0.064 s
%------------------------------------------------------------------------------
