%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:54 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 261 expanded)
%              Number of leaves         :   29 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  330 ( 615 expanded)
%              Number of equality atoms :   61 ( 132 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f762,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f81,f101,f118,f170,f190,f234,f236,f297,f312,f324,f505,f517,f528,f560,f696,f714,f761])).

fof(f761,plain,
    ( spl1_2
    | ~ spl1_40 ),
    inference(avatar_contradiction_clause,[],[f760])).

fof(f760,plain,
    ( $false
    | spl1_2
    | ~ spl1_40 ),
    inference(trivial_inequality_removal,[],[f758])).

fof(f758,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_2
    | ~ spl1_40 ),
    inference(superposition,[],[f49,f730])).

fof(f730,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_40 ),
    inference(resolution,[],[f695,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f695,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_40 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl1_40
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_40])])).

fof(f49,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_2
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f714,plain,
    ( ~ spl1_6
    | ~ spl1_34
    | spl1_38 ),
    inference(avatar_split_clause,[],[f712,f687,f515,f96])).

fof(f96,plain,
    ( spl1_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f515,plain,
    ( spl1_34
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).

fof(f687,plain,
    ( spl1_38
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).

fof(f712,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_38 ),
    inference(resolution,[],[f688,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f688,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_38 ),
    inference(avatar_component_clause,[],[f687])).

fof(f696,plain,
    ( spl1_40
    | ~ spl1_38
    | ~ spl1_25
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f685,f99,f295,f687,f694])).

fof(f295,plain,
    ( spl1_25
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).

fof(f99,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f685,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_7 ),
    inference(superposition,[],[f42,f680])).

fof(f680,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_7 ),
    inference(resolution,[],[f218,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f218,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_7 ),
    inference(resolution,[],[f100,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f560,plain,
    ( spl1_1
    | ~ spl1_33 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | spl1_1
    | ~ spl1_33 ),
    inference(trivial_inequality_removal,[],[f557])).

fof(f557,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_33 ),
    inference(superposition,[],[f46,f535])).

fof(f535,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_33 ),
    inference(resolution,[],[f504,f35])).

fof(f504,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_33 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl1_33
  <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).

fof(f46,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl1_1
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f528,plain,(
    spl1_34 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | spl1_34 ),
    inference(resolution,[],[f516,f29])).

fof(f516,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_34 ),
    inference(avatar_component_clause,[],[f515])).

fof(f517,plain,
    ( ~ spl1_34
    | ~ spl1_6
    | spl1_31 ),
    inference(avatar_split_clause,[],[f512,f495,f96,f515])).

fof(f495,plain,
    ( spl1_31
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).

fof(f512,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl1_31 ),
    inference(resolution,[],[f496,f43])).

fof(f496,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_31 ),
    inference(avatar_component_clause,[],[f495])).

fof(f505,plain,
    ( spl1_33
    | ~ spl1_31
    | ~ spl1_25
    | ~ spl1_6
    | ~ spl1_14
    | ~ spl1_24 ),
    inference(avatar_split_clause,[],[f490,f292,f188,f96,f295,f495,f503])).

fof(f188,plain,
    ( spl1_14
  <=> v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f292,plain,
    ( spl1_24
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f490,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_6
    | ~ spl1_14
    | ~ spl1_24 ),
    inference(superposition,[],[f42,f487])).

fof(f487,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_6
    | ~ spl1_14
    | ~ spl1_24 ),
    inference(forward_demodulation,[],[f486,f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f486,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_6
    | ~ spl1_14
    | ~ spl1_24 ),
    inference(forward_demodulation,[],[f481,f478])).

fof(f478,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_14
    | ~ spl1_24 ),
    inference(forward_demodulation,[],[f477,f339])).

fof(f339,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_24 ),
    inference(resolution,[],[f293,f35])).

fof(f293,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_24 ),
    inference(avatar_component_clause,[],[f292])).

fof(f477,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f476,f203])).

fof(f203,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_14 ),
    inference(resolution,[],[f189,f35])).

fof(f189,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f188])).

fof(f476,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) ),
    inference(resolution,[],[f129,f30])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f129,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k4_relat_1(k5_relat_1(sK0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f89,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f89,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k4_relat_1(k5_relat_1(sK0,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f481,plain,
    ( k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_6 ),
    inference(resolution,[],[f269,f145])).

fof(f145,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f269,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k1_relat_1(k5_relat_1(sK0,X9)) = k2_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) ) ),
    inference(resolution,[],[f76,f29])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(k4_relat_1(k5_relat_1(X1,X0))) ) ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f324,plain,
    ( ~ spl1_6
    | ~ spl1_4
    | spl1_22 ),
    inference(avatar_split_clause,[],[f322,f284,f65,f96])).

fof(f65,plain,
    ( spl1_4
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f284,plain,
    ( spl1_22
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f322,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | spl1_22 ),
    inference(resolution,[],[f285,f43])).

fof(f285,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | spl1_22 ),
    inference(avatar_component_clause,[],[f284])).

fof(f312,plain,(
    spl1_25 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl1_25 ),
    inference(resolution,[],[f296,f30])).

fof(f296,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_25 ),
    inference(avatar_component_clause,[],[f295])).

fof(f297,plain,
    ( spl1_24
    | ~ spl1_22
    | ~ spl1_25
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f279,f229,f295,f284,f292])).

fof(f229,plain,
    ( spl1_17
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f279,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_17 ),
    inference(superposition,[],[f42,f230])).

fof(f230,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f229])).

fof(f236,plain,(
    spl1_18 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl1_18 ),
    inference(resolution,[],[f233,f33])).

fof(f233,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK0))
    | spl1_18 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl1_18
  <=> r1_tarski(k1_xboole_0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f234,plain,
    ( spl1_17
    | ~ spl1_4
    | ~ spl1_18
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f220,f99,f232,f65,f229])).

fof(f220,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_7 ),
    inference(superposition,[],[f100,f57])).

fof(f57,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f38,f29])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f190,plain,
    ( spl1_14
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f186,f143,f188])).

fof(f143,plain,
    ( spl1_12
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f186,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(global_subsumption,[],[f30,f181])).

fof(f181,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f42,f148])).

fof(f148,plain,(
    k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f147,f32])).

fof(f147,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f58,f30])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(resolution,[],[f38,f34])).

fof(f170,plain,
    ( ~ spl1_6
    | spl1_12 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl1_6
    | spl1_12 ),
    inference(resolution,[],[f160,f145])).

fof(f160,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_12 ),
    inference(resolution,[],[f144,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f144,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl1_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f118,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl1_6 ),
    inference(resolution,[],[f110,f30])).

fof(f110,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_6 ),
    inference(resolution,[],[f97,f34])).

fof(f97,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f101,plain,
    ( ~ spl1_6
    | spl1_7 ),
    inference(avatar_split_clause,[],[f94,f99,f96])).

fof(f94,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f91,f31])).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f41,f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f81,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl1_4 ),
    inference(resolution,[],[f74,f29])).

fof(f74,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_4 ),
    inference(resolution,[],[f66,f36])).

fof(f66,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f50,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f28,f48,f45])).

fof(f28,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:38:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.47  % (18610)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.47  % (18601)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.49  % (18593)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (18598)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.11/0.51  % (18612)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.11/0.52  % (18615)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.11/0.52  % (18600)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.11/0.52  % (18613)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.11/0.52  % (18607)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.11/0.52  % (18594)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.11/0.52  % (18605)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.11/0.52  % (18599)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.11/0.53  % (18614)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.11/0.53  % (18609)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.29/0.53  % (18606)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.29/0.53  % (18616)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.29/0.53  % (18596)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.29/0.54  % (18596)Refutation not found, incomplete strategy% (18596)------------------------------
% 1.29/0.54  % (18596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (18596)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (18596)Memory used [KB]: 10490
% 1.29/0.54  % (18596)Time elapsed: 0.119 s
% 1.29/0.54  % (18596)------------------------------
% 1.29/0.54  % (18596)------------------------------
% 1.29/0.54  % (18604)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.29/0.54  % (18597)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.29/0.55  % (18608)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.29/0.55  % (18605)Refutation found. Thanks to Tanya!
% 1.29/0.55  % SZS status Theorem for theBenchmark
% 1.29/0.55  % SZS output start Proof for theBenchmark
% 1.29/0.55  fof(f762,plain,(
% 1.29/0.55    $false),
% 1.29/0.55    inference(avatar_sat_refutation,[],[f50,f81,f101,f118,f170,f190,f234,f236,f297,f312,f324,f505,f517,f528,f560,f696,f714,f761])).
% 1.29/0.55  fof(f761,plain,(
% 1.29/0.55    spl1_2 | ~spl1_40),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f760])).
% 1.29/0.55  fof(f760,plain,(
% 1.29/0.55    $false | (spl1_2 | ~spl1_40)),
% 1.29/0.55    inference(trivial_inequality_removal,[],[f758])).
% 1.29/0.55  fof(f758,plain,(
% 1.29/0.55    k1_xboole_0 != k1_xboole_0 | (spl1_2 | ~spl1_40)),
% 1.29/0.55    inference(superposition,[],[f49,f730])).
% 1.29/0.55  fof(f730,plain,(
% 1.29/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~spl1_40),
% 1.29/0.55    inference(resolution,[],[f695,f35])).
% 1.29/0.55  fof(f35,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.29/0.55    inference(cnf_transformation,[],[f17])).
% 1.29/0.55  fof(f17,plain,(
% 1.29/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f2])).
% 1.29/0.55  fof(f2,axiom,(
% 1.29/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.29/0.55  fof(f695,plain,(
% 1.29/0.55    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_40),
% 1.29/0.55    inference(avatar_component_clause,[],[f694])).
% 1.29/0.55  fof(f694,plain,(
% 1.29/0.55    spl1_40 <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_40])])).
% 1.29/0.55  fof(f49,plain,(
% 1.29/0.55    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_2),
% 1.29/0.55    inference(avatar_component_clause,[],[f48])).
% 1.29/0.55  fof(f48,plain,(
% 1.29/0.55    spl1_2 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.29/0.55  fof(f714,plain,(
% 1.29/0.55    ~spl1_6 | ~spl1_34 | spl1_38),
% 1.29/0.55    inference(avatar_split_clause,[],[f712,f687,f515,f96])).
% 1.29/0.55  fof(f96,plain,(
% 1.29/0.55    spl1_6 <=> v1_relat_1(k1_xboole_0)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.29/0.55  fof(f515,plain,(
% 1.29/0.55    spl1_34 <=> v1_relat_1(sK0)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).
% 1.29/0.55  fof(f687,plain,(
% 1.29/0.55    spl1_38 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).
% 1.29/0.55  fof(f712,plain,(
% 1.29/0.55    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | spl1_38),
% 1.29/0.55    inference(resolution,[],[f688,f43])).
% 1.29/0.55  fof(f43,plain,(
% 1.29/0.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f27])).
% 1.29/0.55  fof(f27,plain,(
% 1.29/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.29/0.55    inference(flattening,[],[f26])).
% 1.29/0.55  fof(f26,plain,(
% 1.29/0.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.29/0.55    inference(ennf_transformation,[],[f6])).
% 1.29/0.55  fof(f6,axiom,(
% 1.29/0.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.29/0.55  fof(f688,plain,(
% 1.29/0.55    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_38),
% 1.29/0.55    inference(avatar_component_clause,[],[f687])).
% 1.29/0.55  fof(f696,plain,(
% 1.29/0.55    spl1_40 | ~spl1_38 | ~spl1_25 | ~spl1_7),
% 1.29/0.55    inference(avatar_split_clause,[],[f685,f99,f295,f687,f694])).
% 1.29/0.55  fof(f295,plain,(
% 1.29/0.55    spl1_25 <=> v1_xboole_0(k1_xboole_0)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).
% 1.29/0.55  fof(f99,plain,(
% 1.29/0.55    spl1_7 <=> ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~r1_tarski(k1_xboole_0,k1_relat_1(X0)))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 1.29/0.55  fof(f685,plain,(
% 1.29/0.55    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_7),
% 1.29/0.55    inference(superposition,[],[f42,f680])).
% 1.29/0.55  fof(f680,plain,(
% 1.29/0.55    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_7),
% 1.29/0.55    inference(resolution,[],[f218,f29])).
% 1.29/0.55  fof(f29,plain,(
% 1.29/0.55    v1_relat_1(sK0)),
% 1.29/0.55    inference(cnf_transformation,[],[f15])).
% 1.29/0.55  fof(f15,plain,(
% 1.29/0.55    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f14])).
% 1.29/0.55  fof(f14,negated_conjecture,(
% 1.29/0.55    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.29/0.55    inference(negated_conjecture,[],[f13])).
% 1.29/0.55  fof(f13,conjecture,(
% 1.29/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.29/0.55  fof(f218,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_7),
% 1.29/0.55    inference(resolution,[],[f100,f33])).
% 1.29/0.55  fof(f33,plain,(
% 1.29/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f3])).
% 1.29/0.55  fof(f3,axiom,(
% 1.29/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.29/0.55  fof(f100,plain,(
% 1.29/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_7),
% 1.29/0.55    inference(avatar_component_clause,[],[f99])).
% 1.29/0.55  fof(f42,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f25])).
% 1.29/0.55  fof(f25,plain,(
% 1.29/0.55    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.29/0.55    inference(flattening,[],[f24])).
% 1.29/0.55  fof(f24,plain,(
% 1.29/0.55    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.29/0.55    inference(ennf_transformation,[],[f7])).
% 1.29/0.55  fof(f7,axiom,(
% 1.29/0.55    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 1.29/0.55  fof(f560,plain,(
% 1.29/0.55    spl1_1 | ~spl1_33),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f559])).
% 1.29/0.55  fof(f559,plain,(
% 1.29/0.55    $false | (spl1_1 | ~spl1_33)),
% 1.29/0.55    inference(trivial_inequality_removal,[],[f557])).
% 1.29/0.55  fof(f557,plain,(
% 1.29/0.55    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_33)),
% 1.29/0.55    inference(superposition,[],[f46,f535])).
% 1.29/0.55  fof(f535,plain,(
% 1.29/0.55    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl1_33),
% 1.29/0.55    inference(resolution,[],[f504,f35])).
% 1.29/0.55  fof(f504,plain,(
% 1.29/0.55    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_33),
% 1.29/0.55    inference(avatar_component_clause,[],[f503])).
% 1.29/0.55  fof(f503,plain,(
% 1.29/0.55    spl1_33 <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).
% 1.29/0.55  fof(f46,plain,(
% 1.29/0.55    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl1_1),
% 1.29/0.55    inference(avatar_component_clause,[],[f45])).
% 1.29/0.55  fof(f45,plain,(
% 1.29/0.55    spl1_1 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.29/0.55  fof(f528,plain,(
% 1.29/0.55    spl1_34),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f526])).
% 1.29/0.55  fof(f526,plain,(
% 1.29/0.55    $false | spl1_34),
% 1.29/0.55    inference(resolution,[],[f516,f29])).
% 1.29/0.55  fof(f516,plain,(
% 1.29/0.55    ~v1_relat_1(sK0) | spl1_34),
% 1.29/0.55    inference(avatar_component_clause,[],[f515])).
% 1.29/0.55  fof(f517,plain,(
% 1.29/0.55    ~spl1_34 | ~spl1_6 | spl1_31),
% 1.29/0.55    inference(avatar_split_clause,[],[f512,f495,f96,f515])).
% 1.29/0.55  fof(f495,plain,(
% 1.29/0.55    spl1_31 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).
% 1.29/0.55  fof(f512,plain,(
% 1.29/0.55    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl1_31),
% 1.29/0.55    inference(resolution,[],[f496,f43])).
% 1.29/0.55  fof(f496,plain,(
% 1.29/0.55    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_31),
% 1.29/0.55    inference(avatar_component_clause,[],[f495])).
% 1.29/0.55  fof(f505,plain,(
% 1.29/0.55    spl1_33 | ~spl1_31 | ~spl1_25 | ~spl1_6 | ~spl1_14 | ~spl1_24),
% 1.29/0.55    inference(avatar_split_clause,[],[f490,f292,f188,f96,f295,f495,f503])).
% 1.29/0.55  fof(f188,plain,(
% 1.29/0.55    spl1_14 <=> v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 1.29/0.55  fof(f292,plain,(
% 1.29/0.55    spl1_24 <=> v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).
% 1.29/0.55  fof(f490,plain,(
% 1.29/0.55    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_6 | ~spl1_14 | ~spl1_24)),
% 1.29/0.55    inference(superposition,[],[f42,f487])).
% 1.29/0.55  fof(f487,plain,(
% 1.29/0.55    k1_xboole_0 = k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_6 | ~spl1_14 | ~spl1_24)),
% 1.29/0.55    inference(forward_demodulation,[],[f486,f32])).
% 1.29/0.55  fof(f32,plain,(
% 1.29/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.29/0.55    inference(cnf_transformation,[],[f12])).
% 1.29/0.55  fof(f12,axiom,(
% 1.29/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.29/0.55  fof(f486,plain,(
% 1.29/0.55    k2_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_6 | ~spl1_14 | ~spl1_24)),
% 1.29/0.55    inference(forward_demodulation,[],[f481,f478])).
% 1.29/0.55  fof(f478,plain,(
% 1.29/0.55    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_14 | ~spl1_24)),
% 1.29/0.55    inference(forward_demodulation,[],[f477,f339])).
% 1.29/0.55  fof(f339,plain,(
% 1.29/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~spl1_24),
% 1.29/0.55    inference(resolution,[],[f293,f35])).
% 1.29/0.55  fof(f293,plain,(
% 1.29/0.55    v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_24),
% 1.29/0.55    inference(avatar_component_clause,[],[f292])).
% 1.29/0.55  fof(f477,plain,(
% 1.29/0.55    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~spl1_14),
% 1.29/0.55    inference(forward_demodulation,[],[f476,f203])).
% 1.29/0.55  fof(f203,plain,(
% 1.29/0.55    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_14),
% 1.29/0.55    inference(resolution,[],[f189,f35])).
% 1.29/0.55  fof(f189,plain,(
% 1.29/0.55    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl1_14),
% 1.29/0.55    inference(avatar_component_clause,[],[f188])).
% 1.29/0.55  fof(f476,plain,(
% 1.29/0.55    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0))),
% 1.29/0.55    inference(resolution,[],[f129,f30])).
% 1.29/0.55  fof(f30,plain,(
% 1.29/0.55    v1_xboole_0(k1_xboole_0)),
% 1.29/0.55    inference(cnf_transformation,[],[f1])).
% 1.29/0.55  fof(f1,axiom,(
% 1.29/0.55    v1_xboole_0(k1_xboole_0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.29/0.55  fof(f129,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k4_relat_1(k5_relat_1(sK0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK0))) )),
% 1.29/0.55    inference(resolution,[],[f89,f34])).
% 1.29/0.55  fof(f34,plain,(
% 1.29/0.55    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f16])).
% 1.29/0.55  fof(f16,plain,(
% 1.29/0.55    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f4])).
% 1.29/0.55  fof(f4,axiom,(
% 1.29/0.55    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.29/0.55  fof(f89,plain,(
% 1.29/0.55    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(sK0,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK0))) )),
% 1.29/0.55    inference(resolution,[],[f40,f29])).
% 1.29/0.55  fof(f40,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f21])).
% 1.29/0.55  fof(f21,plain,(
% 1.29/0.55    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f11])).
% 1.29/0.55  fof(f11,axiom,(
% 1.29/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.29/0.55  fof(f481,plain,(
% 1.29/0.55    k1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_6),
% 1.29/0.55    inference(resolution,[],[f269,f145])).
% 1.29/0.55  fof(f145,plain,(
% 1.29/0.55    v1_relat_1(k1_xboole_0) | ~spl1_6),
% 1.29/0.55    inference(avatar_component_clause,[],[f96])).
% 1.29/0.55  fof(f269,plain,(
% 1.29/0.55    ( ! [X9] : (~v1_relat_1(X9) | k1_relat_1(k5_relat_1(sK0,X9)) = k2_relat_1(k4_relat_1(k5_relat_1(sK0,X9)))) )),
% 1.29/0.55    inference(resolution,[],[f76,f29])).
% 1.29/0.55  fof(f76,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) )),
% 1.29/0.55    inference(resolution,[],[f43,f39])).
% 1.29/0.55  fof(f39,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f20])).
% 1.29/0.55  fof(f20,plain,(
% 1.29/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f9])).
% 1.29/0.55  fof(f9,axiom,(
% 1.29/0.55    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.29/0.55  fof(f324,plain,(
% 1.29/0.55    ~spl1_6 | ~spl1_4 | spl1_22),
% 1.29/0.55    inference(avatar_split_clause,[],[f322,f284,f65,f96])).
% 1.29/0.55  fof(f65,plain,(
% 1.29/0.55    spl1_4 <=> v1_relat_1(k4_relat_1(sK0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.29/0.55  fof(f284,plain,(
% 1.29/0.55    spl1_22 <=> v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 1.29/0.55  fof(f322,plain,(
% 1.29/0.55    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | spl1_22),
% 1.29/0.55    inference(resolution,[],[f285,f43])).
% 1.29/0.55  fof(f285,plain,(
% 1.29/0.55    ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | spl1_22),
% 1.29/0.55    inference(avatar_component_clause,[],[f284])).
% 1.29/0.55  fof(f312,plain,(
% 1.29/0.55    spl1_25),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f311])).
% 1.29/0.55  fof(f311,plain,(
% 1.29/0.55    $false | spl1_25),
% 1.29/0.55    inference(resolution,[],[f296,f30])).
% 1.29/0.55  fof(f296,plain,(
% 1.29/0.55    ~v1_xboole_0(k1_xboole_0) | spl1_25),
% 1.29/0.55    inference(avatar_component_clause,[],[f295])).
% 1.29/0.55  fof(f297,plain,(
% 1.29/0.55    spl1_24 | ~spl1_22 | ~spl1_25 | ~spl1_17),
% 1.29/0.55    inference(avatar_split_clause,[],[f279,f229,f295,f284,f292])).
% 1.29/0.55  fof(f229,plain,(
% 1.29/0.55    spl1_17 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 1.29/0.55  fof(f279,plain,(
% 1.29/0.55    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_17),
% 1.29/0.55    inference(superposition,[],[f42,f230])).
% 1.29/0.55  fof(f230,plain,(
% 1.29/0.55    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_17),
% 1.29/0.55    inference(avatar_component_clause,[],[f229])).
% 1.29/0.55  fof(f236,plain,(
% 1.29/0.55    spl1_18),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f235])).
% 1.29/0.55  fof(f235,plain,(
% 1.29/0.55    $false | spl1_18),
% 1.29/0.55    inference(resolution,[],[f233,f33])).
% 1.29/0.55  fof(f233,plain,(
% 1.29/0.55    ~r1_tarski(k1_xboole_0,k2_relat_1(sK0)) | spl1_18),
% 1.29/0.55    inference(avatar_component_clause,[],[f232])).
% 1.29/0.55  fof(f232,plain,(
% 1.29/0.55    spl1_18 <=> r1_tarski(k1_xboole_0,k2_relat_1(sK0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 1.29/0.55  fof(f234,plain,(
% 1.29/0.55    spl1_17 | ~spl1_4 | ~spl1_18 | ~spl1_7),
% 1.29/0.55    inference(avatar_split_clause,[],[f220,f99,f232,f65,f229])).
% 1.29/0.55  fof(f220,plain,(
% 1.29/0.55    ~r1_tarski(k1_xboole_0,k2_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~spl1_7),
% 1.29/0.55    inference(superposition,[],[f100,f57])).
% 1.29/0.55  fof(f57,plain,(
% 1.29/0.55    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 1.29/0.55    inference(resolution,[],[f38,f29])).
% 1.29/0.55  fof(f38,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f20])).
% 1.29/0.55  fof(f190,plain,(
% 1.29/0.55    spl1_14 | ~spl1_12),
% 1.29/0.55    inference(avatar_split_clause,[],[f186,f143,f188])).
% 1.29/0.55  fof(f143,plain,(
% 1.29/0.55    spl1_12 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.29/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 1.29/0.55  fof(f186,plain,(
% 1.29/0.55    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.29/0.55    inference(global_subsumption,[],[f30,f181])).
% 1.29/0.55  fof(f181,plain,(
% 1.29/0.55    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 1.29/0.55    inference(superposition,[],[f42,f148])).
% 1.29/0.55  fof(f148,plain,(
% 1.29/0.55    k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.29/0.55    inference(forward_demodulation,[],[f147,f32])).
% 1.29/0.55  fof(f147,plain,(
% 1.29/0.55    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.29/0.55    inference(resolution,[],[f58,f30])).
% 1.29/0.55  fof(f58,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.29/0.55    inference(resolution,[],[f38,f34])).
% 1.29/0.55  fof(f170,plain,(
% 1.29/0.55    ~spl1_6 | spl1_12),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f168])).
% 1.29/0.55  fof(f168,plain,(
% 1.29/0.55    $false | (~spl1_6 | spl1_12)),
% 1.29/0.55    inference(resolution,[],[f160,f145])).
% 1.29/0.55  fof(f160,plain,(
% 1.29/0.55    ~v1_relat_1(k1_xboole_0) | spl1_12),
% 1.29/0.55    inference(resolution,[],[f144,f36])).
% 1.29/0.55  fof(f36,plain,(
% 1.29/0.55    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f18])).
% 1.29/0.55  fof(f18,plain,(
% 1.29/0.55    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f5])).
% 1.29/0.55  fof(f5,axiom,(
% 1.29/0.55    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.29/0.55  fof(f144,plain,(
% 1.29/0.55    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl1_12),
% 1.29/0.55    inference(avatar_component_clause,[],[f143])).
% 1.29/0.55  fof(f118,plain,(
% 1.29/0.55    spl1_6),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f117])).
% 1.29/0.55  fof(f117,plain,(
% 1.29/0.55    $false | spl1_6),
% 1.29/0.55    inference(resolution,[],[f110,f30])).
% 1.29/0.55  fof(f110,plain,(
% 1.29/0.55    ~v1_xboole_0(k1_xboole_0) | spl1_6),
% 1.29/0.55    inference(resolution,[],[f97,f34])).
% 1.29/0.55  fof(f97,plain,(
% 1.29/0.55    ~v1_relat_1(k1_xboole_0) | spl1_6),
% 1.29/0.55    inference(avatar_component_clause,[],[f96])).
% 1.29/0.55  fof(f101,plain,(
% 1.29/0.55    ~spl1_6 | spl1_7),
% 1.29/0.55    inference(avatar_split_clause,[],[f94,f99,f96])).
% 1.29/0.55  fof(f94,plain,(
% 1.29/0.55    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.29/0.55    inference(forward_demodulation,[],[f91,f31])).
% 1.29/0.55  fof(f31,plain,(
% 1.29/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.29/0.55    inference(cnf_transformation,[],[f12])).
% 1.29/0.55  fof(f91,plain,(
% 1.29/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.29/0.55    inference(superposition,[],[f41,f32])).
% 1.29/0.55  fof(f41,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f23])).
% 1.29/0.55  fof(f23,plain,(
% 1.29/0.55    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.29/0.55    inference(flattening,[],[f22])).
% 1.29/0.55  fof(f22,plain,(
% 1.29/0.55    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.29/0.55    inference(ennf_transformation,[],[f10])).
% 1.29/0.55  fof(f10,axiom,(
% 1.29/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.29/0.55  fof(f81,plain,(
% 1.29/0.55    spl1_4),
% 1.29/0.55    inference(avatar_contradiction_clause,[],[f79])).
% 1.29/0.55  fof(f79,plain,(
% 1.29/0.55    $false | spl1_4),
% 1.29/0.55    inference(resolution,[],[f74,f29])).
% 1.29/0.55  fof(f74,plain,(
% 1.29/0.55    ~v1_relat_1(sK0) | spl1_4),
% 1.29/0.55    inference(resolution,[],[f66,f36])).
% 1.29/0.55  fof(f66,plain,(
% 1.29/0.55    ~v1_relat_1(k4_relat_1(sK0)) | spl1_4),
% 1.29/0.55    inference(avatar_component_clause,[],[f65])).
% 1.29/0.55  fof(f50,plain,(
% 1.29/0.55    ~spl1_1 | ~spl1_2),
% 1.29/0.55    inference(avatar_split_clause,[],[f28,f48,f45])).
% 1.29/0.55  fof(f28,plain,(
% 1.29/0.55    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.29/0.55    inference(cnf_transformation,[],[f15])).
% 1.29/0.55  % SZS output end Proof for theBenchmark
% 1.29/0.55  % (18605)------------------------------
% 1.29/0.55  % (18605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (18605)Termination reason: Refutation
% 1.29/0.55  
% 1.29/0.55  % (18605)Memory used [KB]: 11001
% 1.29/0.55  % (18605)Time elapsed: 0.141 s
% 1.29/0.55  % (18605)------------------------------
% 1.29/0.55  % (18605)------------------------------
% 1.29/0.55  % (18592)Success in time 0.183 s
%------------------------------------------------------------------------------
