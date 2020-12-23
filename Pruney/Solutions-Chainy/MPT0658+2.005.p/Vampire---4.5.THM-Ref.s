%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 182 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :    8
%              Number of atoms          :  336 ( 620 expanded)
%              Number of equality atoms :   36 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f47,f51,f55,f59,f63,f69,f83,f98,f106,f114,f122,f129])).

fof(f129,plain,
    ( ~ spl1_9
    | ~ spl1_10
    | spl1_14
    | ~ spl1_15
    | ~ spl1_16
    | ~ spl1_17 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl1_9
    | ~ spl1_10
    | spl1_14
    | ~ spl1_15
    | ~ spl1_16
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f127,f97])).

fof(f97,plain,
    ( sK0 != k2_funct_1(k4_relat_1(sK0))
    | spl1_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl1_14
  <=> sK0 = k2_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f127,plain,
    ( sK0 = k2_funct_1(k4_relat_1(sK0))
    | ~ spl1_9
    | ~ spl1_10
    | ~ spl1_15
    | ~ spl1_16
    | ~ spl1_17 ),
    inference(forward_demodulation,[],[f126,f68])).

fof(f68,plain,
    ( sK0 = k4_relat_1(k4_relat_1(sK0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl1_10
  <=> sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f126,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = k2_funct_1(k4_relat_1(sK0))
    | ~ spl1_9
    | ~ spl1_15
    | ~ spl1_16
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f125,f105])).

fof(f105,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl1_15
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f125,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = k2_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_9
    | ~ spl1_16
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f124,f113])).

fof(f113,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl1_16
  <=> v1_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f124,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = k2_funct_1(k4_relat_1(sK0))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_9
    | ~ spl1_17 ),
    inference(resolution,[],[f121,f62])).

fof(f62,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | k4_relat_1(X0) = k2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl1_9
  <=> ! [X0] :
        ( k4_relat_1(X0) = k2_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f121,plain,
    ( v2_funct_1(k4_relat_1(sK0))
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl1_17
  <=> v2_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f122,plain,
    ( spl1_17
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f117,f80,f49,f40,f35,f30,f119])).

fof(f30,plain,
    ( spl1_2
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f35,plain,
    ( spl1_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f40,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f49,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v2_funct_1(k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f80,plain,
    ( spl1_12
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f117,plain,
    ( v2_funct_1(k4_relat_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f116,f42])).

fof(f42,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f116,plain,
    ( v2_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f115,f37])).

fof(f37,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f115,plain,
    ( v2_funct_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_6
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f93,f32])).

fof(f32,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f93,plain,
    ( v2_funct_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_6
    | ~ spl1_12 ),
    inference(superposition,[],[f50,f82])).

fof(f82,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f50,plain,
    ( ! [X0] :
        ( v2_funct_1(k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f114,plain,
    ( spl1_16
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f109,f80,f53,f40,f35,f30,f111])).

fof(f53,plain,
    ( spl1_7
  <=> ! [X0] :
        ( v1_funct_1(k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f109,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f108,f42])).

fof(f108,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f107,f37])).

fof(f107,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f92,f32])).

fof(f92,plain,
    ( v1_funct_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(superposition,[],[f54,f82])).

fof(f54,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f106,plain,
    ( spl1_15
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f101,f80,f57,f40,f35,f30,f103])).

fof(f57,plain,
    ( spl1_8
  <=> ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f101,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f100,f42])).

fof(f100,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f99,f37])).

fof(f99,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f91,f32])).

fof(f91,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(superposition,[],[f58,f82])).

fof(f58,plain,
    ( ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f98,plain,
    ( ~ spl1_14
    | spl1_1
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f90,f80,f25,f95])).

fof(f25,plain,
    ( spl1_1
  <=> sK0 = k2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f90,plain,
    ( sK0 != k2_funct_1(k4_relat_1(sK0))
    | spl1_1
    | ~ spl1_12 ),
    inference(superposition,[],[f27,f82])).

fof(f27,plain,
    ( sK0 != k2_funct_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f83,plain,
    ( spl1_12
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f78,f61,f40,f35,f30,f80])).

fof(f78,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f77,f42])).

fof(f77,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f75,f37])).

fof(f75,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(resolution,[],[f62,f32])).

fof(f69,plain,
    ( spl1_10
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f64,f45,f40,f66])).

fof(f45,plain,
    ( spl1_5
  <=> ! [X0] :
        ( k4_relat_1(k4_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f64,plain,
    ( sK0 = k4_relat_1(k4_relat_1(sK0))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(resolution,[],[f46,f42])).

fof(f46,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k4_relat_1(X0)) = X0 )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f63,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f59,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f20,f57])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f55,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f43,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f15,f40])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK0 != k2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k2_funct_1(k2_funct_1(X0)) != X0
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( sK0 != k2_funct_1(k2_funct_1(sK0))
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f38,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f18,f25])).

fof(f18,plain,(
    sK0 != k2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:00:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (5033)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (5034)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (5033)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f47,f51,f55,f59,f63,f69,f83,f98,f106,f114,f122,f129])).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    ~spl1_9 | ~spl1_10 | spl1_14 | ~spl1_15 | ~spl1_16 | ~spl1_17),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f128])).
% 0.21/0.42  fof(f128,plain,(
% 0.21/0.42    $false | (~spl1_9 | ~spl1_10 | spl1_14 | ~spl1_15 | ~spl1_16 | ~spl1_17)),
% 0.21/0.42    inference(subsumption_resolution,[],[f127,f97])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    sK0 != k2_funct_1(k4_relat_1(sK0)) | spl1_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f95])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    spl1_14 <=> sK0 = k2_funct_1(k4_relat_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.42  fof(f127,plain,(
% 0.21/0.42    sK0 = k2_funct_1(k4_relat_1(sK0)) | (~spl1_9 | ~spl1_10 | ~spl1_15 | ~spl1_16 | ~spl1_17)),
% 0.21/0.42    inference(forward_demodulation,[],[f126,f68])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    sK0 = k4_relat_1(k4_relat_1(sK0)) | ~spl1_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl1_10 <=> sK0 = k4_relat_1(k4_relat_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    k4_relat_1(k4_relat_1(sK0)) = k2_funct_1(k4_relat_1(sK0)) | (~spl1_9 | ~spl1_15 | ~spl1_16 | ~spl1_17)),
% 0.21/0.42    inference(subsumption_resolution,[],[f125,f105])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    v1_relat_1(k4_relat_1(sK0)) | ~spl1_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f103])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl1_15 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    k4_relat_1(k4_relat_1(sK0)) = k2_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_9 | ~spl1_16 | ~spl1_17)),
% 0.21/0.42    inference(subsumption_resolution,[],[f124,f113])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    v1_funct_1(k4_relat_1(sK0)) | ~spl1_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f111])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    spl1_16 <=> v1_funct_1(k4_relat_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    k4_relat_1(k4_relat_1(sK0)) = k2_funct_1(k4_relat_1(sK0)) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_9 | ~spl1_17)),
% 0.21/0.42    inference(resolution,[],[f121,f62])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl1_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f61])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl1_9 <=> ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    v2_funct_1(k4_relat_1(sK0)) | ~spl1_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f119])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    spl1_17 <=> v2_funct_1(k4_relat_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.42  fof(f122,plain,(
% 0.21/0.42    spl1_17 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_6 | ~spl1_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f117,f80,f49,f40,f35,f30,f119])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl1_2 <=> v2_funct_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl1_3 <=> v1_funct_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl1_4 <=> v1_relat_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl1_6 <=> ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl1_12 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    v2_funct_1(k4_relat_1(sK0)) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_6 | ~spl1_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f116,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    v1_relat_1(sK0) | ~spl1_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f40])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    v2_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_3 | ~spl1_6 | ~spl1_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f115,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    v1_funct_1(sK0) | ~spl1_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f35])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    v2_funct_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_6 | ~spl1_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f93,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    v2_funct_1(sK0) | ~spl1_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    v2_funct_1(k4_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_6 | ~spl1_12)),
% 0.21/0.42    inference(superposition,[],[f50,f82])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f80])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl1_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f49])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    spl1_16 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_7 | ~spl1_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f109,f80,f53,f40,f35,f30,f111])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl1_7 <=> ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    v1_funct_1(k4_relat_1(sK0)) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_7 | ~spl1_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f108,f42])).
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_3 | ~spl1_7 | ~spl1_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f107,f37])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    v1_funct_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_7 | ~spl1_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f92,f32])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    v1_funct_1(k4_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_7 | ~spl1_12)),
% 0.21/0.42    inference(superposition,[],[f54,f82])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl1_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    spl1_15 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_8 | ~spl1_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f101,f80,f57,f40,f35,f30,f103])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl1_8 <=> ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    v1_relat_1(k4_relat_1(sK0)) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_8 | ~spl1_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f100,f42])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_3 | ~spl1_8 | ~spl1_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f99,f37])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_8 | ~spl1_12)),
% 0.21/0.42    inference(subsumption_resolution,[],[f91,f32])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    v1_relat_1(k4_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_8 | ~spl1_12)),
% 0.21/0.42    inference(superposition,[],[f58,f82])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl1_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    ~spl1_14 | spl1_1 | ~spl1_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f90,f80,f25,f95])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    spl1_1 <=> sK0 = k2_funct_1(k2_funct_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    sK0 != k2_funct_1(k4_relat_1(sK0)) | (spl1_1 | ~spl1_12)),
% 0.21/0.42    inference(superposition,[],[f27,f82])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    sK0 != k2_funct_1(k2_funct_1(sK0)) | spl1_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f25])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl1_12 | ~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f78,f61,f40,f35,f30,f80])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    k2_funct_1(sK0) = k4_relat_1(sK0) | (~spl1_2 | ~spl1_3 | ~spl1_4 | ~spl1_9)),
% 0.21/0.42    inference(subsumption_resolution,[],[f77,f42])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_3 | ~spl1_9)),
% 0.21/0.42    inference(subsumption_resolution,[],[f75,f37])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_2 | ~spl1_9)),
% 0.21/0.42    inference(resolution,[],[f62,f32])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    spl1_10 | ~spl1_4 | ~spl1_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f45,f40,f66])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl1_5 <=> ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    sK0 = k4_relat_1(k4_relat_1(sK0)) | (~spl1_4 | ~spl1_5)),
% 0.21/0.42    inference(resolution,[],[f46,f42])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) ) | ~spl1_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f45])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl1_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f61])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl1_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f57])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl1_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f53])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl1_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl1_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f45])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl1_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f40])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    sK0 != k2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (sK0 != k2_funct_1(k2_funct_1(sK0)) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0] : ((k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f35])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    v1_funct_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f30])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    v2_funct_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ~spl1_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f25])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    sK0 != k2_funct_1(k2_funct_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (5033)------------------------------
% 0.21/0.42  % (5033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (5033)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (5033)Memory used [KB]: 10618
% 0.21/0.42  % (5033)Time elapsed: 0.008 s
% 0.21/0.42  % (5033)------------------------------
% 0.21/0.42  % (5033)------------------------------
% 0.21/0.42  % (5026)Success in time 0.065 s
%------------------------------------------------------------------------------
