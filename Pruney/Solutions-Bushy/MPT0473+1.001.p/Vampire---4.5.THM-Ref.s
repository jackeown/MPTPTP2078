%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0473+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  97 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  159 ( 295 expanded)
%              Number of equality atoms :   75 ( 160 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f28,f33,f38,f43,f47,f51,f58,f63,f66,f70])).

fof(f70,plain,
    ( spl1_8
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f69,f49,f30,f20,f55])).

fof(f55,plain,
    ( spl1_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f20,plain,
    ( spl1_1
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f30,plain,
    ( spl1_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f49,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f69,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_1
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f68,f21])).

fof(f21,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f68,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl1_3
    | ~ spl1_7 ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f66,plain,
    ( spl1_2
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl1_2
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f64,f37])).

fof(f37,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f64,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl1_2
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f26,f57])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f26,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl1_2
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f63,plain,
    ( spl1_1
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl1_1
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f60,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl1_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f60,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl1_1
    | ~ spl1_8 ),
    inference(superposition,[],[f22,f57])).

fof(f22,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f58,plain,
    ( spl1_8
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f53,f45,f30,f24,f55])).

fof(f45,plain,
    ( spl1_6
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(subsumption_resolution,[],[f52,f25])).

fof(f25,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f52,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f51,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f17,f49])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f47,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f43,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f15,f40])).

fof(f15,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f38,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( k1_xboole_0 != k2_relat_1(sK0)
      | k1_xboole_0 != k1_relat_1(sK0) )
    & ( k1_xboole_0 = k2_relat_1(sK0)
      | k1_xboole_0 = k1_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k2_relat_1(sK0)
        | k1_xboole_0 != k1_relat_1(sK0) )
      & ( k1_xboole_0 = k2_relat_1(sK0)
        | k1_xboole_0 = k1_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <~> k1_xboole_0 = k2_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k1_relat_1(X0)
        <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f28,plain,
    ( spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f13,f24,f20])).

fof(f13,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f14,f24,f20])).

fof(f14,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 != k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
