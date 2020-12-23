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
% DateTime   : Thu Dec  3 12:53:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
% (14917)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
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
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:43:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (14910)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (14926)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (14923)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (14909)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (14907)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (14907)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (14908)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (14915)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (14918)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  % (14917)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f60,f65,f70,f75,f94,f114,f125,f138,f144,f150])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ~spl2_1 | ~spl2_2 | spl2_15),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f149])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    $false | (~spl2_1 | ~spl2_2 | spl2_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    v1_relat_1(sK0) | ~spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    spl2_1 <=> v1_relat_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~v1_relat_1(sK0) | (~spl2_2 | spl2_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f146,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    v1_funct_1(sK0) | ~spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    spl2_2 <=> v1_funct_1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl2_15),
% 0.22/0.51    inference(resolution,[],[f137,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ~v1_funct_1(k2_funct_1(sK0)) | spl2_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f135])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl2_15 <=> v1_funct_1(k2_funct_1(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ~spl2_1 | ~spl2_2 | spl2_14),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f143])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    $false | (~spl2_1 | ~spl2_2 | spl2_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f142,f39])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    ~v1_relat_1(sK0) | (~spl2_2 | spl2_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f140,f44])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl2_14),
% 0.22/0.51    inference(resolution,[],[f133,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK0)) | spl2_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f131])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    spl2_14 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ~spl2_14 | ~spl2_15 | spl2_6 | ~spl2_10 | ~spl2_12 | ~spl2_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f129,f123,f111,f91,f62,f135,f131])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    spl2_6 <=> k2_funct_1(sK0) = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl2_10 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    spl2_12 <=> k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    spl2_13 <=> ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | (spl2_6 | ~spl2_10 | ~spl2_12 | ~spl2_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f128,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    k2_funct_1(sK0) != sK1 | spl2_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f62])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    k2_funct_1(sK0) = sK1 | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | (~spl2_10 | ~spl2_12 | ~spl2_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f127,f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~spl2_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f111])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0)) | k2_funct_1(sK0) = sK1 | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | (~spl2_10 | ~spl2_13)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f126])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) | k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0)) | k2_funct_1(sK0) = sK1 | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | (~spl2_10 | ~spl2_13)),
% 0.22/0.52    inference(superposition,[],[f124,f93])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl2_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f91])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | sK1 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f123])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    spl2_13 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f103,f72,f67,f52,f47,f42,f37,f123])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    spl2_3 <=> v1_relat_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    spl2_4 <=> v1_funct_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl2_7 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl2_8 <=> k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8)),
% 0.22/0.52    inference(forward_demodulation,[],[f102,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl2_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f67])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f101,f39])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f100,f44])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_4 | ~spl2_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f99,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    v1_relat_1(sK1) | ~spl2_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f47])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_4 | ~spl2_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f98,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    v1_funct_1(sK1) | ~spl2_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f52])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | k5_relat_1(X0,sK0) != k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_8),
% 0.22/0.52    inference(superposition,[],[f35,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) | ~spl2_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f72])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X2,X3,X1] : (k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1)) | X1 = X3 | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    spl2_12 | ~spl2_1 | ~spl2_2 | ~spl2_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f97,f57,f42,f37,f111])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl2_5 <=> v2_funct_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f96,f39])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_2 | ~spl2_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f95,f44])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_5),
% 0.22/0.52    inference(resolution,[],[f33,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    v2_funct_1(sK0) | ~spl2_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f57])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    spl2_10 | ~spl2_1 | ~spl2_2 | ~spl2_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f81,f57,f42,f37,f91])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | (~spl2_1 | ~spl2_2 | ~spl2_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f80,f39])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_2 | ~spl2_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f79,f44])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_5),
% 0.22/0.52    inference(resolution,[],[f31,f59])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl2_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f72])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    (k2_funct_1(sK0) != sK1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f18,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,X1) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,X1) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    spl2_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f25,f67])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ~spl2_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f62])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    k2_funct_1(sK0) != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    spl2_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f24,f57])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    v2_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl2_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f23,f52])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    v1_funct_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    spl2_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f22,f47])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    v1_relat_1(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    spl2_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f21,f42])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    v1_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    spl2_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f20,f37])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (14907)------------------------------
% 0.22/0.52  % (14907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14907)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (14907)Memory used [KB]: 6140
% 0.22/0.52  % (14907)Time elapsed: 0.097 s
% 0.22/0.52  % (14907)------------------------------
% 0.22/0.52  % (14907)------------------------------
% 0.22/0.52  % (14921)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (14904)Success in time 0.154 s
%------------------------------------------------------------------------------
