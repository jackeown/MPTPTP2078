%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 150 expanded)
%              Number of leaves         :   27 (  68 expanded)
%              Depth                    :    7
%              Number of atoms          :  251 ( 438 expanded)
%              Number of equality atoms :   47 (  64 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f68,f72,f79,f83,f99,f103,f107,f115,f161,f196,f238,f243,f327,f334])).

fof(f334,plain,
    ( ~ spl2_15
    | spl2_20
    | ~ spl2_24
    | ~ spl2_25
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl2_15
    | spl2_20
    | ~ spl2_24
    | ~ spl2_25
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f281,f329])).

fof(f329,plain,
    ( k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_25
    | ~ spl2_34 ),
    inference(unit_resulting_resolution,[],[f242,f326])).

fof(f326,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl2_34
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f242,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl2_25
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f281,plain,
    ( k1_xboole_0 != k1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_15
    | spl2_20
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f195,f237,f106])).

fof(f106,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_15
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f237,plain,
    ( ! [X10] : v1_relat_1(k3_xboole_0(sK0,X10))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl2_24
  <=> ! [X10] : v1_relat_1(k3_xboole_0(sK0,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f195,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl2_20 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl2_20
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f327,plain,
    ( spl2_34
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f135,f101,f66,f325])).

fof(f66,plain,
    ( spl2_6
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f101,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f135,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f102,f67])).

% (11756)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f67,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f243,plain,
    ( spl2_25
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f174,f159,f77,f57,f47,f42,f240])).

fof(f42,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f57,plain,
    ( spl2_4
  <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f77,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f159,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f174,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f165,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f59,f78])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f59,plain,
    ( r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f165,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f44,f49,f160])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f49,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f44,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f238,plain,
    ( spl2_24
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f154,f113,f97,f236])).

fof(f97,plain,
    ( spl2_13
  <=> ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f113,plain,
    ( spl2_17
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f154,plain,
    ( ! [X10] : v1_relat_1(k3_xboole_0(sK0,X10))
    | ~ spl2_13
    | ~ spl2_17 ),
    inference(superposition,[],[f98,f114])).

fof(f114,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f98,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f196,plain,
    ( ~ spl2_20
    | spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f117,f81,f52,f193])).

fof(f52,plain,
    ( spl2_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f81,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f117,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f54,f82])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f54,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f161,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f32,f159])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f115,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f33,f113])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f107,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f30,f105])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f103,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f40,f101])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f99,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f73,f70,f42,f97])).

fof(f70,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( v1_relat_1(k4_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f73,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f44,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k4_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f83,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f79,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f35,f77])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f34,f70])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f68,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f60,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(f55,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f47])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (11758)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (11753)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (11759)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (11757)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (11758)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (11767)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (11765)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f335,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f68,f72,f79,f83,f99,f103,f107,f115,f161,f196,f238,f243,f327,f334])).
% 0.21/0.47  fof(f334,plain,(
% 0.21/0.47    ~spl2_15 | spl2_20 | ~spl2_24 | ~spl2_25 | ~spl2_34),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f333])).
% 0.21/0.47  fof(f333,plain,(
% 0.21/0.47    $false | (~spl2_15 | spl2_20 | ~spl2_24 | ~spl2_25 | ~spl2_34)),
% 0.21/0.47    inference(subsumption_resolution,[],[f281,f329])).
% 0.21/0.47  fof(f329,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_25 | ~spl2_34)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f242,f326])).
% 0.21/0.47  fof(f326,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl2_34),
% 0.21/0.47    inference(avatar_component_clause,[],[f325])).
% 0.21/0.47  fof(f325,plain,(
% 0.21/0.47    spl2_34 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.47  fof(f242,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | ~spl2_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f240])).
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    spl2_25 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    k1_xboole_0 != k1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_15 | spl2_20 | ~spl2_24)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f195,f237,f106])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl2_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    spl2_15 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    ( ! [X10] : (v1_relat_1(k3_xboole_0(sK0,X10))) ) | ~spl2_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f236])).
% 0.21/0.47  fof(f236,plain,(
% 0.21/0.47    spl2_24 <=> ! [X10] : v1_relat_1(k3_xboole_0(sK0,X10))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.47  fof(f195,plain,(
% 0.21/0.47    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl2_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f193])).
% 0.21/0.47  fof(f193,plain,(
% 0.21/0.47    spl2_20 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.47  fof(f327,plain,(
% 0.21/0.47    spl2_34 | ~spl2_6 | ~spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f135,f101,f66,f325])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl2_6 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl2_14 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl2_6 | ~spl2_14)),
% 0.21/0.47    inference(superposition,[],[f102,f67])).
% 0.21/0.47  % (11756)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f66])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) ) | ~spl2_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f101])).
% 0.21/0.47  fof(f243,plain,(
% 0.21/0.47    spl2_25 | ~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_8 | ~spl2_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f174,f159,f77,f57,f47,f42,f240])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl2_4 <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl2_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    spl2_18 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) | (~spl2_1 | ~spl2_2 | ~spl2_4 | ~spl2_8 | ~spl2_18)),
% 0.21/0.47    inference(forward_demodulation,[],[f165,f116])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl2_4 | ~spl2_8)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f59,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f77])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) | (~spl2_1 | ~spl2_2 | ~spl2_18)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f44,f49,f160])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f159])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    v1_relat_1(sK0) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f42])).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    spl2_24 | ~spl2_13 | ~spl2_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f154,f113,f97,f236])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    spl2_13 <=> ! [X0] : v1_relat_1(k4_xboole_0(sK0,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    spl2_17 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    ( ! [X10] : (v1_relat_1(k3_xboole_0(sK0,X10))) ) | (~spl2_13 | ~spl2_17)),
% 0.21/0.47    inference(superposition,[],[f98,f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f113])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK0,X0))) ) | ~spl2_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f97])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    ~spl2_20 | spl2_3 | ~spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f117,f81,f52,f193])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl2_3 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl2_9 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    k1_xboole_0 != k3_xboole_0(sK0,sK1) | (spl2_3 | ~spl2_9)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f54,f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,sK1) | spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    spl2_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f159])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl2_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f113])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    spl2_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f105])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f101])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl2_13 | ~spl2_1 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f73,f70,f42,f97])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl2_7 <=> ! [X1,X0] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK0,X0))) ) | (~spl2_1 | ~spl2_7)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f44,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f70])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f81])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f77])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f70])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f66])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f57])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f52])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f47])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f42])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (11758)------------------------------
% 0.21/0.47  % (11758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11758)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (11758)Memory used [KB]: 6268
% 0.21/0.47  % (11758)Time elapsed: 0.058 s
% 0.21/0.47  % (11758)------------------------------
% 0.21/0.47  % (11758)------------------------------
% 0.21/0.47  % (11752)Success in time 0.118 s
%------------------------------------------------------------------------------
