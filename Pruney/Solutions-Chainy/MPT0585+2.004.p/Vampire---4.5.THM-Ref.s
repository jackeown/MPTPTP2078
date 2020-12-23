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
% DateTime   : Thu Dec  3 12:50:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 123 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :    6
%              Number of atoms          :  174 ( 297 expanded)
%              Number of equality atoms :   55 (  97 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f38,f42,f49,f59,f63,f69,f73,f81,f89,f108,f114,f127])).

fof(f127,plain,
    ( ~ spl2_5
    | ~ spl2_9
    | spl2_15
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_9
    | spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f107,f125])).

fof(f125,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f121,f48])).

fof(f48,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_5
  <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f121,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(superposition,[],[f113,f68])).

fof(f68,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f113,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl2_16
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f107,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1))))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_15
  <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f114,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f109,f87,f26,f112])).

fof(f26,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f87,plain,
    ( spl2_13
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f109,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(resolution,[],[f88,f28])).

fof(f28,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f108,plain,
    ( ~ spl2_15
    | spl2_7
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f94,f79,f71,f56,f105])).

fof(f56,plain,
    ( spl2_7
  <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f71,plain,
    ( spl2_10
  <=> ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f79,plain,
    ( spl2_11
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f94,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1))))
    | spl2_7
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f58,f92])).

fof(f92,plain,
    ( k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(superposition,[],[f80,f72])).

fof(f72,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f80,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f58,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f89,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f24,f87])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f81,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f74,f67,f36,f79])).

fof(f36,plain,
    ( spl2_3
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f74,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK0)))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(superposition,[],[f68,f37])).

fof(f37,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f73,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f65,f61,f31,f71])).

fof(f31,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f61,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f65,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X1))
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(resolution,[],[f62,f33])).

fof(f33,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f69,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f64,f61,f26,f67])).

fof(f64,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(resolution,[],[f62,f28])).

fof(f63,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f59,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f17,f56])).

fof(f17,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f49,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f43,f40,f26,f46])).

fof(f40,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f43,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,k1_relat_1(X0)) = X0 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f42,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f38,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f34,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (18364)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.42  % (18364)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f129,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f29,f34,f38,f42,f49,f59,f63,f69,f73,f81,f89,f108,f114,f127])).
% 0.20/0.42  fof(f127,plain,(
% 0.20/0.42    ~spl2_5 | ~spl2_9 | spl2_15 | ~spl2_16),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.42  fof(f126,plain,(
% 0.20/0.42    $false | (~spl2_5 | ~spl2_9 | spl2_15 | ~spl2_16)),
% 0.20/0.42    inference(subsumption_resolution,[],[f107,f125])).
% 0.20/0.42  fof(f125,plain,(
% 0.20/0.42    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl2_5 | ~spl2_9 | ~spl2_16)),
% 0.20/0.42    inference(forward_demodulation,[],[f121,f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl2_5 <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f121,plain,(
% 0.20/0.42    ( ! [X0] : (k7_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)),X0) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,X0)))) ) | (~spl2_9 | ~spl2_16)),
% 0.20/0.42    inference(superposition,[],[f113,f68])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))) ) | ~spl2_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f67])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    spl2_9 <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.42  fof(f113,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl2_16),
% 0.20/0.42    inference(avatar_component_clause,[],[f112])).
% 0.20/0.42  fof(f112,plain,(
% 0.20/0.42    spl2_16 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.42  fof(f107,plain,(
% 0.20/0.42    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1)))) | spl2_15),
% 0.20/0.42    inference(avatar_component_clause,[],[f105])).
% 0.20/0.42  fof(f105,plain,(
% 0.20/0.42    spl2_15 <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    spl2_16 | ~spl2_1 | ~spl2_13),
% 0.20/0.42    inference(avatar_split_clause,[],[f109,f87,f26,f112])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    spl2_1 <=> v1_relat_1(sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl2_13 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1)))) ) | (~spl2_1 | ~spl2_13)),
% 0.20/0.42    inference(resolution,[],[f88,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    v1_relat_1(sK0) | ~spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f26])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl2_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f87])).
% 0.20/0.42  fof(f108,plain,(
% 0.20/0.42    ~spl2_15 | spl2_7 | ~spl2_10 | ~spl2_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f94,f79,f71,f56,f105])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    spl2_7 <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl2_10 <=> ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    spl2_11 <=> ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1)))) | (spl2_7 | ~spl2_10 | ~spl2_11)),
% 0.20/0.42    inference(backward_demodulation,[],[f58,f92])).
% 0.20/0.42  fof(f92,plain,(
% 0.20/0.42    k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))) = k1_relat_1(k7_relat_1(sK0,k1_relat_1(sK1))) | (~spl2_10 | ~spl2_11)),
% 0.20/0.42    inference(superposition,[],[f80,f72])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X1))) ) | ~spl2_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f71])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK0)))) ) | ~spl2_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f79])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) | spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f56])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    spl2_13),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f87])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f22,f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    spl2_11 | ~spl2_3 | ~spl2_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f74,f67,f36,f79])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    spl2_3 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK0)))) ) | (~spl2_3 | ~spl2_9)),
% 0.20/0.42    inference(superposition,[],[f68,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f36])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    spl2_10 | ~spl2_2 | ~spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f65,f61,f31,f71])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    spl2_2 <=> v1_relat_1(sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl2_8 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X1))) ) | (~spl2_2 | ~spl2_8)),
% 0.20/0.42    inference(resolution,[],[f62,f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f31])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) ) | ~spl2_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f61])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    spl2_9 | ~spl2_1 | ~spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f64,f61,f26,f67])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK0),X0))) ) | (~spl2_1 | ~spl2_8)),
% 0.20/0.42    inference(resolution,[],[f62,f28])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl2_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f61])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f21,f20])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    ~spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f17,f56])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) => (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl2_5 | ~spl2_1 | ~spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f43,f40,f26,f46])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl2_4 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | (~spl2_1 | ~spl2_4)),
% 0.20/0.42    inference(resolution,[],[f41,f28])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f40])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f40])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f36])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f31])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    v1_relat_1(sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f26])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    v1_relat_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (18364)------------------------------
% 0.20/0.42  % (18364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (18364)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (18364)Memory used [KB]: 6140
% 0.20/0.42  % (18364)Time elapsed: 0.009 s
% 0.20/0.42  % (18364)------------------------------
% 0.20/0.42  % (18364)------------------------------
% 0.20/0.43  % (18356)Success in time 0.068 s
%------------------------------------------------------------------------------
