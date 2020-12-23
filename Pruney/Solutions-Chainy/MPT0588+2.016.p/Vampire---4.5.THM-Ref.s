%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 110 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :  164 ( 246 expanded)
%              Number of equality atoms :   50 (  80 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f50,f61,f74,f78,f83,f88,f93,f102])).

fof(f102,plain,
    ( ~ spl2_2
    | ~ spl2_5
    | spl2_9
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_5
    | spl2_9
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f73,f100])).

fof(f100,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f99,f82])).

fof(f82,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_relat_1(sK1,X0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_11
  <=> ! [X0] : k7_relat_1(sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_relat_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f99,plain,
    ( ! [X0] : k1_setfam_1(k2_tarski(sK1,k7_relat_1(sK1,X0))) = k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f95,f35])).

fof(f35,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_2
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f95,plain,
    ( ! [X0] : k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),sK1))
    | ~ spl2_5
    | ~ spl2_13 ),
    inference(superposition,[],[f92,f49])).

fof(f49,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_5
  <=> sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f92,plain,
    ( ! [X0,X1] : k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_13
  <=> ! [X1,X0] : k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f73,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_9
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f93,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f89,f86,f29,f91])).

fof(f29,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f89,plain,
    ( ! [X0,X1] : k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f87,f31])).

fof(f31,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f87,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f26,f86])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f23,f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

fof(f83,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f79,f76,f29,f81])).

fof(f76,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k7_relat_1(X0,X1)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f79,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_relat_1(sK1,X0)))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(resolution,[],[f77,f31])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k7_relat_1(X0,X1))) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f64,f59,f38,f34,f76])).

fof(f38,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k1_setfam_1(k2_tarski(X0,X1)) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k7_relat_1(X0,X1)))
        | ~ v1_relat_1(X0) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f62,f35])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(k7_relat_1(X0,X1),X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_setfam_1(k2_tarski(X0,X1)) = X0 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f74,plain,(
    ~ spl2_9 ),
    inference(avatar_split_clause,[],[f27,f71])).

fof(f27,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f24,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f24,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f17,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f61,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f50,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f45,f42,f29,f47])).

fof(f42,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f45,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f43,f31])).

fof(f43,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,k1_relat_1(X0)) = X0 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f44,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f40,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f32,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:22:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (30266)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.42  % (30266)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f50,f61,f74,f78,f83,f88,f93,f102])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    ~spl2_2 | ~spl2_5 | spl2_9 | ~spl2_11 | ~spl2_13),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    $false | (~spl2_2 | ~spl2_5 | spl2_9 | ~spl2_11 | ~spl2_13)),
% 0.21/0.42    inference(subsumption_resolution,[],[f73,f100])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))))) ) | (~spl2_2 | ~spl2_5 | ~spl2_11 | ~spl2_13)),
% 0.21/0.42    inference(forward_demodulation,[],[f99,f82])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ( ! [X0] : (k7_relat_1(sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_relat_1(sK1,X0)))) ) | ~spl2_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f81])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    spl2_11 <=> ! [X0] : k7_relat_1(sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_relat_1(sK1,X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,k7_relat_1(sK1,X0))) = k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))))) ) | (~spl2_2 | ~spl2_5 | ~spl2_13)),
% 0.21/0.42    inference(forward_demodulation,[],[f95,f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    spl2_2 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    ( ! [X0] : (k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),sK1))) ) | (~spl2_5 | ~spl2_13)),
% 0.21/0.42    inference(superposition,[],[f92,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl2_5 <=> sK1 = k7_relat_1(sK1,k1_relat_1(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)))) ) | ~spl2_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f91])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl2_13 <=> ! [X1,X0] : k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))) | spl2_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f71])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    spl2_9 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl2_13 | ~spl2_1 | ~spl2_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f89,f86,f29,f91])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    spl2_12 <=> ! [X1,X0,X2] : (k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)))) ) | (~spl2_1 | ~spl2_12)),
% 0.21/0.42    inference(resolution,[],[f87,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f29])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))) ) | ~spl2_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f86])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    spl2_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f86])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f23,f20,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl2_11 | ~spl2_1 | ~spl2_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f79,f76,f29,f81])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl2_10 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k7_relat_1(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ( ! [X0] : (k7_relat_1(sK1,X0) = k1_setfam_1(k2_tarski(sK1,k7_relat_1(sK1,X0)))) ) | (~spl2_1 | ~spl2_10)),
% 0.21/0.42    inference(resolution,[],[f77,f31])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k7_relat_1(X0,X1)))) ) | ~spl2_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f76])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl2_10 | ~spl2_2 | ~spl2_3 | ~spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f59,f38,f34,f76])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl2_3 <=> ! [X1,X0] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl2_7 <=> ! [X1,X0] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(X0,k7_relat_1(X0,X1))) | ~v1_relat_1(X0)) ) | (~spl2_2 | ~spl2_3 | ~spl2_7)),
% 0.21/0.42    inference(forward_demodulation,[],[f62,f35])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_setfam_1(k2_tarski(k7_relat_1(X0,X1),X0)) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_7)),
% 0.21/0.42    inference(resolution,[],[f60,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) ) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) ) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f59])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    ~spl2_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f71])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))))),
% 0.21/0.42    inference(backward_demodulation,[],[f24,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)))),
% 0.21/0.42    inference(definition_unfolding,[],[f17,f20])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f59])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f22,f20])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl2_5 | ~spl2_1 | ~spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f45,f42,f29,f47])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl2_4 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) | (~spl2_1 | ~spl2_4)),
% 0.21/0.42    inference(resolution,[],[f43,f31])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f42])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f38])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f34])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f29])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (30266)------------------------------
% 0.21/0.42  % (30266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (30266)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (30266)Memory used [KB]: 6140
% 0.21/0.42  % (30266)Time elapsed: 0.006 s
% 0.21/0.42  % (30266)------------------------------
% 0.21/0.42  % (30266)------------------------------
% 0.21/0.42  % (30258)Success in time 0.062 s
%------------------------------------------------------------------------------
