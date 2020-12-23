%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  97 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  167 ( 247 expanded)
%              Number of equality atoms :   30 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f43,f52,f64,f68,f80,f97,f116,f121,f126])).

fof(f126,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f38,f124])).

fof(f124,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f122,f92])).

fof(f92,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f89,f81])).

fof(f81,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f33,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f33,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f89,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f63,f51])).

fof(f51,plain,
    ( ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_5
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f63,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

% (7303)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f62,plain,
    ( spl2_8
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f122,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f33,f120,f96])).

fof(f96,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f120,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl2_14
  <=> ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f38,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_2
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f121,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f117,f114,f78,f31,f119])).

fof(f114,plain,
    ( spl2_13
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f117,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f115,f81])).

fof(f115,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f74,f66,f31,f114])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f74,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f33,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f97,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f29,f95])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f80,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f28,f78])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f64,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f48,f41,f31,f62])).

fof(f41,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f48,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f33,f42])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f26,f41])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f39,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f21,f36])).

fof(f21,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f34,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f31])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:49:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (7306)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (7306)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f127,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f34,f39,f43,f52,f64,f68,f80,f97,f116,f121,f126])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    ~spl2_1 | spl2_2 | ~spl2_5 | ~spl2_8 | ~spl2_10 | ~spl2_11 | ~spl2_14),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    $false | (~spl2_1 | spl2_2 | ~spl2_5 | ~spl2_8 | ~spl2_10 | ~spl2_11 | ~spl2_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f38,f124])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))) ) | (~spl2_1 | ~spl2_5 | ~spl2_8 | ~spl2_10 | ~spl2_11 | ~spl2_14)),
% 0.21/0.46    inference(forward_demodulation,[],[f122,f92])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0))) ) | (~spl2_1 | ~spl2_5 | ~spl2_8 | ~spl2_10)),
% 0.21/0.46    inference(forward_demodulation,[],[f89,f81])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | (~spl2_1 | ~spl2_10)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f33,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl2_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl2_10 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) ) | (~spl2_5 | ~spl2_8)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f63,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl2_5 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f62])).
% 0.21/0.47  % (7303)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl2_8 <=> ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X0] : (k7_relat_1(k7_relat_1(sK1,X0),k3_xboole_0(k1_relat_1(sK1),X0)) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))) ) | (~spl2_1 | ~spl2_11 | ~spl2_14)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f33,f120,f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) ) | ~spl2_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f95])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl2_11 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)) ) | ~spl2_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl2_14 <=> ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) | spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    spl2_2 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl2_14 | ~spl2_1 | ~spl2_10 | ~spl2_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f117,f114,f78,f31,f119])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl2_13 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK1),X0),X0)) ) | (~spl2_1 | ~spl2_10 | ~spl2_13)),
% 0.21/0.47    inference(forward_demodulation,[],[f115,f81])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) ) | ~spl2_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f114])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl2_13 | ~spl2_1 | ~spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f74,f66,f31,f114])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl2_9 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_9)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f33,f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f66])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    spl2_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f95])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f78])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f66])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl2_8 | ~spl2_1 | ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f48,f41,f31,f62])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl2_3 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | (~spl2_1 | ~spl2_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f33,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f50])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f41])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f36])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f31])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (7306)------------------------------
% 0.21/0.47  % (7306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7306)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (7306)Memory used [KB]: 6140
% 0.21/0.47  % (7306)Time elapsed: 0.011 s
% 0.21/0.47  % (7306)------------------------------
% 0.21/0.47  % (7306)------------------------------
% 0.21/0.47  % (7301)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (7300)Success in time 0.109 s
%------------------------------------------------------------------------------
