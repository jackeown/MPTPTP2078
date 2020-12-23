%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0656+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 195 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  407 ( 997 expanded)
%              Number of equality atoms :  109 ( 314 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f60,f65,f70,f75,f94,f114,f125,f138,f144,f150])).

fof(f150,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_15 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_15 ),
    inference(subsumption_resolution,[],[f148,f39])).

fof(f39,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f148,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_2
    | spl2_15 ),
    inference(subsumption_resolution,[],[f146,f44])).

fof(f44,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f146,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_15 ),
    inference(resolution,[],[f137,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f137,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl2_15
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f144,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_14 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_14 ),
    inference(subsumption_resolution,[],[f142,f39])).

fof(f142,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_2
    | spl2_14 ),
    inference(subsumption_resolution,[],[f140,f44])).

fof(f140,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl2_14 ),
    inference(resolution,[],[f133,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f133,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl2_14
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f138,plain,
    ( ~ spl2_14
    | ~ spl2_15
    | spl2_6
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f129,f123,f111,f91,f62,f135,f131])).

fof(f62,plain,
    ( spl2_6
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f91,plain,
    ( spl2_10
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f111,plain,
    ( spl2_12
  <=> k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f123,plain,
    ( spl2_13
  <=> ! [X0] :
        ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
        | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f129,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_6
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f128,f64])).

fof(f64,plain,
    ( k2_funct_1(sK0) != sK1
    | spl2_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f128,plain,
    ( k2_funct_1(sK0) = sK1
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f127,f113])).

fof(f113,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f127,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
    | k2_funct_1(sK0) = sK1
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
    | k2_funct_1(sK0) = sK1
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(superposition,[],[f124,f93])).

fof(f93,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f124,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
        | sK1 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f103,f72,f67,f52,f47,f42,f37,f123])).

fof(f47,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f52,plain,
    ( spl2_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f67,plain,
    ( spl2_7
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f72,plain,
    ( spl2_8
  <=> k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f103,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
        | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f102,f69])).

fof(f69,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f102,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f101,f39])).

fof(f101,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f100,f44])).

fof(f100,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f99,f49])).

fof(f49,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f99,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f98,f54])).

fof(f54,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f98,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_8 ),
    inference(superposition,[],[f35,f74])).

fof(f74,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f35,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1))
      | X1 = X3
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_relat_1(X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X2,X3) = k6_relat_1(X0)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).

fof(f114,plain,
    ( spl2_12
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f97,f57,f42,f37,f111])).

fof(f57,plain,
    ( spl2_5
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f97,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f96,f39])).

fof(f96,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f95,f44])).

fof(f95,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f33,f59])).

fof(f59,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f94,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f81,f57,f42,f37,f91])).

fof(f81,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f79,f44])).

fof(f79,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f31,f59])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f75,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f72])).

fof(f26,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,X1)
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,X1)
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f70,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f67])).

fof(f25,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f57])).

% (20072)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f37])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
