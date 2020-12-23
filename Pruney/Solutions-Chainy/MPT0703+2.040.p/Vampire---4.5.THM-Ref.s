%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 134 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  222 ( 433 expanded)
%              Number of equality atoms :   42 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f63,f67,f71,f82,f87,f91,f112,f127,f146,f155])).

fof(f155,plain,
    ( ~ spl3_1
    | ~ spl3_10
    | spl3_11
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_10
    | spl3_11
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f113,f147])).

fof(f147,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(superposition,[],[f145,f126])).

fof(f126,plain,
    ( k1_xboole_0 = k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_16
  <=> k1_xboole_0 = k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f145,plain,
    ( ! [X0,X1] : k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_18
  <=> ! [X1,X0] : k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f113,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_10
    | spl3_11
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f34,f86,f111,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k10_relat_1(X1,X0)
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k10_relat_1(X1,X0)
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f111,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k2_relat_1(sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_14
  <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f86,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f34,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f146,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f92,f89,f37,f32,f144])).

fof(f37,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f89,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f92,plain,
    ( ! [X0,X1] : k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f34,f39,f90])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f39,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f127,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f74,f65,f52,f124])).

fof(f52,plain,
    ( spl3_5
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f74,plain,
    ( k1_xboole_0 = k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f54,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f54,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f112,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f76,f69,f47,f110])).

fof(f47,plain,
    ( spl3_4
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f76,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k2_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f49,f70])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k4_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f49,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

% (31825)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f91,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f30,f89])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f29,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f28,f23])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f87,plain,
    ( ~ spl3_11
    | spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f72,f61,f42,f84])).

fof(f42,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f72,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_3
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f44,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f44,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f82,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f24,f80])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f67,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (31834)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (31835)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (31832)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (31826)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (31826)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f63,f67,f71,f82,f87,f91,f112,f127,f146,f155])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    ~spl3_1 | ~spl3_10 | spl3_11 | ~spl3_14 | ~spl3_16 | ~spl3_18),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f154])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    $false | (~spl3_1 | ~spl3_10 | spl3_11 | ~spl3_14 | ~spl3_16 | ~spl3_18)),
% 0.20/0.47    inference(subsumption_resolution,[],[f113,f147])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    k1_xboole_0 = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | (~spl3_16 | ~spl3_18)),
% 0.20/0.47    inference(superposition,[],[f145,f126])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl3_16 <=> k1_xboole_0 = k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))) ) | ~spl3_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f144])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    spl3_18 <=> ! [X1,X0] : k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    k1_xboole_0 != k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_10 | spl3_11 | ~spl3_14)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f34,f86,f111,f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) ) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl3_10 <=> ! [X1,X0] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k2_relat_1(sK2))) ) | ~spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f110])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl3_14 <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k2_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f84])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    spl3_18 | ~spl3_1 | ~spl3_2 | ~spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f92,f89,f37,f32,f144])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    spl3_2 <=> v1_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl3_12 <=> ! [X1,X0,X2] : (k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_12)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f34,f39,f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f89])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    v1_funct_1(sK2) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f37])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    spl3_16 | ~spl3_5 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f74,f65,f52,f124])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    spl3_5 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl3_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | (~spl3_5 | ~spl3_8)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f54,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f65])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f52])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    spl3_14 | ~spl3_4 | ~spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f76,f69,f47,f110])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    spl3_4 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl3_9 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k2_relat_1(sK2))) ) | (~spl3_4 | ~spl3_9)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f49,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f69])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f47])).
% 0.20/0.47  % (31825)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f89])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k4_xboole_0(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f29,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f28,f23])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ~spl3_11 | spl3_3 | ~spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f72,f61,f42,f84])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl3_7 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_3 | ~spl3_7)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f44,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f61])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK1) | spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f42])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f24,f80])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f69])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f65])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f61])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f52])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.47  fof(f6,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f47])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f42])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f37])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f32])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (31826)------------------------------
% 0.20/0.47  % (31826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31826)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (31826)Memory used [KB]: 6140
% 0.20/0.47  % (31826)Time elapsed: 0.060 s
% 0.20/0.47  % (31826)------------------------------
% 0.20/0.47  % (31826)------------------------------
% 0.20/0.47  % (31829)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (31819)Success in time 0.114 s
%------------------------------------------------------------------------------
