%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:54 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  246 ( 499 expanded)
%              Number of leaves         :   48 ( 196 expanded)
%              Depth                    :   23
%              Number of atoms          : 1038 (2643 expanded)
%              Number of equality atoms :  228 ( 740 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f166,f178,f184,f200,f241,f248,f258,f305,f325,f335,f356,f368,f436,f450,f472,f493,f607,f1112])).

fof(f1112,plain,
    ( ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | ~ spl4_23
    | ~ spl4_30
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(avatar_contradiction_clause,[],[f1111])).

fof(f1111,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | ~ spl4_23
    | ~ spl4_30
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(trivial_inequality_removal,[],[f1110])).

fof(f1110,plain,
    ( k6_relat_1(sK1) != k6_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | ~ spl4_23
    | ~ spl4_30
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1109,f469])).

fof(f469,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f467])).

fof(f467,plain,
    ( spl4_40
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1109,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | ~ spl4_23
    | ~ spl4_30
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1108,f255])).

fof(f255,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f1108,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | ~ spl4_30
    | ~ spl4_44 ),
    inference(trivial_inequality_removal,[],[f1107])).

fof(f1107,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | ~ spl4_30
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1106,f353])).

fof(f353,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl4_30
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f1106,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1105,f119])).

fof(f119,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1105,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1104,f183])).

fof(f183,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1104,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | spl4_16
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1103,f159])).

fof(f159,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1103,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_9
    | ~ spl4_14
    | spl4_16
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1102,f177])).

fof(f177,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1102,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_9
    | spl4_16
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1101,f144])).

fof(f144,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1101,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | spl4_16
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f1091,f199])).

fof(f199,plain,
    ( sK3 != k4_relat_1(sK2)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl4_16
  <=> sK3 = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1091,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | sK3 = k4_relat_1(sK2)
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_44 ),
    inference(superposition,[],[f600,f492])).

fof(f492,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f490])).

fof(f490,plain,
    ( spl4_44
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f600,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k4_relat_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f599,f190])).

fof(f190,plain,(
    ! [X2] :
      ( v1_relat_1(k4_relat_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X2] :
      ( v1_relat_1(k4_relat_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f70,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f599,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1))
      | k4_relat_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f597,f191])).

fof(f191,plain,(
    ! [X1] :
      ( v1_funct_1(k4_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X1] :
      ( v1_funct_1(k4_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f71,f69])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f597,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1))
      | k4_relat_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f592])).

fof(f592,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1))
      | k4_relat_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f338,f217])).

fof(f217,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k4_relat_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k4_relat_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f68,f69])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f338,plain,(
    ! [X2,X0,X1] :
      ( k6_relat_1(k1_relat_1(X2)) != k5_relat_1(k4_relat_1(X0),X1)
      | k4_relat_1(X0) = X2
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f99,f86])).

fof(f86,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f607,plain,
    ( ~ spl4_7
    | ~ spl4_10
    | spl4_43 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_10
    | spl4_43 ),
    inference(unit_resulting_resolution,[],[f149,f134,f488,f293])).

fof(f293,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f88,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f488,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_43 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl4_43
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f134,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f493,plain,
    ( ~ spl4_43
    | spl4_44
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f474,f332,f490,f486])).

fof(f332,plain,
    ( spl4_29
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f474,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_29 ),
    inference(resolution,[],[f265,f334])).

fof(f334,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f332])).

fof(f265,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f79,f167])).

fof(f167,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f81,f82])).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f472,plain,
    ( spl4_40
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f471,f447,f181,f467])).

fof(f447,plain,
    ( spl4_39
  <=> sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f471,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f463,f183])).

fof(f463,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_39 ),
    inference(superposition,[],[f85,f449])).

fof(f449,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f447])).

fof(f85,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f450,plain,
    ( spl4_39
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f445,f431,f181,f157,f117,f447])).

fof(f431,plain,
    ( spl4_38
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f445,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f444,f183])).

fof(f444,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f443,f159])).

fof(f443,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f442,f119])).

fof(f442,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_38 ),
    inference(superposition,[],[f433,f69])).

fof(f433,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f431])).

fof(f436,plain,
    ( spl4_38
    | ~ spl4_28
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f435,f365,f322,f431])).

fof(f322,plain,
    ( spl4_28
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f365,plain,
    ( spl4_31
  <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f435,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_28
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f419,f324])).

fof(f324,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f322])).

fof(f419,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_31 ),
    inference(superposition,[],[f90,f367])).

fof(f367,plain,
    ( sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f365])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f368,plain,
    ( spl4_31
    | spl4_3
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f363,f322,f302,f112,f365])).

fof(f112,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f302,plain,
    ( spl4_26
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f363,plain,
    ( sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | spl4_3
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f362,f114])).

fof(f114,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f362,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f358,f304])).

fof(f304,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f302])).

fof(f358,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_28 ),
    inference(resolution,[],[f324,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f356,plain,
    ( spl4_30
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f355,f245,f147,f351])).

fof(f245,plain,
    ( spl4_22
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f355,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f347,f149])).

fof(f347,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_22 ),
    inference(superposition,[],[f90,f247])).

fof(f247,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f245])).

fof(f335,plain,
    ( spl4_29
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f330,f163,f157,f147,f142,f132,f332])).

fof(f163,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f330,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f329,f159])).

fof(f329,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f328,f149])).

fof(f328,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f327,f144])).

fof(f327,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f326,f134])).

fof(f326,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f165,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f165,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f325,plain,
    ( spl4_28
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f320,f157,f152,f147,f127,f117,f322])).

fof(f127,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f152,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f320,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f319,f159])).

fof(f319,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f318,f154])).

fof(f154,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f318,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f317,f149])).

fof(f317,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f316,f119])).

fof(f316,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f315])).

fof(f315,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f66,f129])).

fof(f129,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f305,plain,
    ( spl4_26
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f300,f157,f152,f147,f127,f117,f302])).

fof(f300,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f299,f159])).

fof(f299,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f298,f154])).

fof(f298,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f297,f149])).

fof(f297,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f296,f119])).

fof(f296,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f295])).

fof(f295,plain,
    ( sK1 != sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f65,f129])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f258,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f257,f238,f132,f253])).

fof(f238,plain,
    ( spl4_21
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f257,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f250,f134])).

fof(f250,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_21 ),
    inference(superposition,[],[f90,f240])).

fof(f240,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f238])).

fof(f248,plain,
    ( spl4_22
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f243,f152,f147,f107,f245])).

fof(f107,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f243,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f242,f109])).

fof(f109,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f242,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f233,f154])).

fof(f233,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f73,f149])).

fof(f241,plain,
    ( spl4_21
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f236,f137,f132,f112,f238])).

fof(f137,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f236,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f235,f114])).

fof(f235,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f232,f139])).

fof(f139,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f232,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f73,f134])).

fof(f200,plain,
    ( ~ spl4_16
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f195,f181,f157,f117,f102,f197])).

fof(f102,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f195,plain,
    ( sK3 != k4_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f194,f183])).

fof(f194,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f193,f159])).

fof(f193,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f186,f119])).

fof(f186,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(superposition,[],[f104,f69])).

fof(f104,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f184,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f179,f147,f181])).

fof(f179,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f171,f92])).

fof(f92,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f171,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f91,f149])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f178,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f173,f132,f175])).

fof(f173,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f170,f92])).

fof(f170,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f91,f134])).

fof(f166,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f161,f122,f163])).

fof(f122,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f161,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f124,f82])).

fof(f124,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f160,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f52,f157])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f48,f47])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f155,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f53,f152])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f150,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f54,f147])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f145,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f55,f142])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f140,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f56,f137])).

fof(f56,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f135,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f57,f132])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f130,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f58,f127])).

fof(f58,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f125,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f59,f122])).

fof(f59,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f120,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f60,f117])).

fof(f60,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f115,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f61,f112])).

fof(f61,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f49])).

fof(f110,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f62,f107])).

fof(f62,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f63,f102])).

fof(f63,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (25465)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (25457)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (25441)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.57  % (25442)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (25448)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (25438)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.57  % (25439)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.58  % (25446)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.58  % (25458)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.58  % (25440)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.59  % (25459)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.59  % (25451)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.60  % (25436)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.60  % (25463)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.60  % (25444)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.60  % (25443)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.61  % (25456)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.76/0.61  % (25455)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.76/0.61  % (25464)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.76/0.61  % (25446)Refutation not found, incomplete strategy% (25446)------------------------------
% 1.76/0.61  % (25446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.62  % (25449)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.76/0.62  % (25462)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.76/0.62  % (25460)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.76/0.62  % (25437)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.76/0.62  % (25450)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.76/0.62  % (25447)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.76/0.62  % (25452)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.76/0.62  % (25446)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.62  
% 1.76/0.62  % (25446)Memory used [KB]: 11257
% 1.76/0.62  % (25446)Time elapsed: 0.188 s
% 1.76/0.62  % (25446)------------------------------
% 1.76/0.62  % (25446)------------------------------
% 1.76/0.63  % (25461)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.00/0.63  % (25454)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.00/0.63  % (25453)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.00/0.65  % (25452)Refutation not found, incomplete strategy% (25452)------------------------------
% 2.00/0.65  % (25452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.65  % (25452)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.65  
% 2.00/0.65  % (25452)Memory used [KB]: 10746
% 2.00/0.65  % (25452)Time elapsed: 0.202 s
% 2.00/0.65  % (25452)------------------------------
% 2.00/0.65  % (25452)------------------------------
% 2.00/0.66  % (25445)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.00/0.66  % (25457)Refutation found. Thanks to Tanya!
% 2.00/0.66  % SZS status Theorem for theBenchmark
% 2.22/0.66  % SZS output start Proof for theBenchmark
% 2.22/0.66  fof(f1113,plain,(
% 2.22/0.66    $false),
% 2.22/0.66    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f166,f178,f184,f200,f241,f248,f258,f305,f325,f335,f356,f368,f436,f450,f472,f493,f607,f1112])).
% 2.22/0.66  fof(f1112,plain,(
% 2.22/0.66    ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | spl4_16 | ~spl4_23 | ~spl4_30 | ~spl4_40 | ~spl4_44),
% 2.22/0.66    inference(avatar_contradiction_clause,[],[f1111])).
% 2.22/0.66  fof(f1111,plain,(
% 2.22/0.66    $false | (~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | spl4_16 | ~spl4_23 | ~spl4_30 | ~spl4_40 | ~spl4_44)),
% 2.22/0.66    inference(trivial_inequality_removal,[],[f1110])).
% 2.22/0.66  fof(f1110,plain,(
% 2.22/0.66    k6_relat_1(sK1) != k6_relat_1(sK1) | (~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | spl4_16 | ~spl4_23 | ~spl4_30 | ~spl4_40 | ~spl4_44)),
% 2.22/0.66    inference(forward_demodulation,[],[f1109,f469])).
% 2.22/0.66  fof(f469,plain,(
% 2.22/0.66    sK1 = k2_relat_1(sK2) | ~spl4_40),
% 2.22/0.66    inference(avatar_component_clause,[],[f467])).
% 2.22/0.66  fof(f467,plain,(
% 2.22/0.66    spl4_40 <=> sK1 = k2_relat_1(sK2)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 2.22/0.66  fof(f1109,plain,(
% 2.22/0.66    k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(sK1) | (~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | spl4_16 | ~spl4_23 | ~spl4_30 | ~spl4_44)),
% 2.22/0.66    inference(forward_demodulation,[],[f1108,f255])).
% 2.22/0.66  fof(f255,plain,(
% 2.22/0.66    sK1 = k1_relat_1(sK3) | ~spl4_23),
% 2.22/0.66    inference(avatar_component_clause,[],[f253])).
% 2.22/0.66  fof(f253,plain,(
% 2.22/0.66    spl4_23 <=> sK1 = k1_relat_1(sK3)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.22/0.66  fof(f1108,plain,(
% 2.22/0.66    k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | (~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | spl4_16 | ~spl4_30 | ~spl4_44)),
% 2.22/0.66    inference(trivial_inequality_removal,[],[f1107])).
% 2.22/0.66  fof(f1107,plain,(
% 2.22/0.66    k6_relat_1(sK0) != k6_relat_1(sK0) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | (~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | spl4_16 | ~spl4_30 | ~spl4_44)),
% 2.22/0.66    inference(forward_demodulation,[],[f1106,f353])).
% 2.22/0.66  fof(f353,plain,(
% 2.22/0.66    sK0 = k1_relat_1(sK2) | ~spl4_30),
% 2.22/0.66    inference(avatar_component_clause,[],[f351])).
% 2.22/0.66  fof(f351,plain,(
% 2.22/0.66    spl4_30 <=> sK0 = k1_relat_1(sK2)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.22/0.66  fof(f1106,plain,(
% 2.22/0.66    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | (~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | spl4_16 | ~spl4_44)),
% 2.22/0.66    inference(subsumption_resolution,[],[f1105,f119])).
% 2.22/0.66  fof(f119,plain,(
% 2.22/0.66    v2_funct_1(sK2) | ~spl4_4),
% 2.22/0.66    inference(avatar_component_clause,[],[f117])).
% 2.22/0.66  fof(f117,plain,(
% 2.22/0.66    spl4_4 <=> v2_funct_1(sK2)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.22/0.66  fof(f1105,plain,(
% 2.22/0.66    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK2) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | spl4_16 | ~spl4_44)),
% 2.22/0.66    inference(subsumption_resolution,[],[f1104,f183])).
% 2.22/0.66  fof(f183,plain,(
% 2.22/0.66    v1_relat_1(sK2) | ~spl4_15),
% 2.22/0.66    inference(avatar_component_clause,[],[f181])).
% 2.22/0.66  fof(f181,plain,(
% 2.22/0.66    spl4_15 <=> v1_relat_1(sK2)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.22/0.66  fof(f1104,plain,(
% 2.22/0.66    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (~spl4_9 | ~spl4_12 | ~spl4_14 | spl4_16 | ~spl4_44)),
% 2.22/0.66    inference(subsumption_resolution,[],[f1103,f159])).
% 2.22/0.66  fof(f159,plain,(
% 2.22/0.66    v1_funct_1(sK2) | ~spl4_12),
% 2.22/0.66    inference(avatar_component_clause,[],[f157])).
% 2.22/0.66  fof(f157,plain,(
% 2.22/0.66    spl4_12 <=> v1_funct_1(sK2)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.22/0.66  fof(f1103,plain,(
% 2.22/0.66    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (~spl4_9 | ~spl4_14 | spl4_16 | ~spl4_44)),
% 2.22/0.66    inference(subsumption_resolution,[],[f1102,f177])).
% 2.22/0.66  fof(f177,plain,(
% 2.22/0.66    v1_relat_1(sK3) | ~spl4_14),
% 2.22/0.66    inference(avatar_component_clause,[],[f175])).
% 2.22/0.66  fof(f175,plain,(
% 2.22/0.66    spl4_14 <=> v1_relat_1(sK3)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.22/0.66  fof(f1102,plain,(
% 2.22/0.66    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (~spl4_9 | spl4_16 | ~spl4_44)),
% 2.22/0.66    inference(subsumption_resolution,[],[f1101,f144])).
% 2.22/0.66  fof(f144,plain,(
% 2.22/0.66    v1_funct_1(sK3) | ~spl4_9),
% 2.22/0.66    inference(avatar_component_clause,[],[f142])).
% 2.22/0.66  fof(f142,plain,(
% 2.22/0.66    spl4_9 <=> v1_funct_1(sK3)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.22/0.66  fof(f1101,plain,(
% 2.22/0.66    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (spl4_16 | ~spl4_44)),
% 2.22/0.66    inference(subsumption_resolution,[],[f1091,f199])).
% 2.22/0.66  fof(f199,plain,(
% 2.22/0.66    sK3 != k4_relat_1(sK2) | spl4_16),
% 2.22/0.66    inference(avatar_component_clause,[],[f197])).
% 2.22/0.66  fof(f197,plain,(
% 2.22/0.66    spl4_16 <=> sK3 = k4_relat_1(sK2)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.22/0.66  fof(f1091,plain,(
% 2.22/0.66    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | sK3 = k4_relat_1(sK2) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | ~spl4_44),
% 2.22/0.66    inference(superposition,[],[f600,f492])).
% 2.22/0.66  fof(f492,plain,(
% 2.22/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_44),
% 2.22/0.66    inference(avatar_component_clause,[],[f490])).
% 2.22/0.66  fof(f490,plain,(
% 2.22/0.66    spl4_44 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.22/0.66  fof(f600,plain,(
% 2.22/0.66    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k4_relat_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0)) )),
% 2.22/0.66    inference(subsumption_resolution,[],[f599,f190])).
% 2.22/0.66  fof(f190,plain,(
% 2.22/0.66    ( ! [X2] : (v1_relat_1(k4_relat_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.22/0.66    inference(duplicate_literal_removal,[],[f189])).
% 2.22/0.66  fof(f189,plain,(
% 2.22/0.66    ( ! [X2] : (v1_relat_1(k4_relat_1(X2)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.22/0.66    inference(superposition,[],[f70,f69])).
% 2.22/0.66  fof(f69,plain,(
% 2.22/0.66    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f28])).
% 2.22/0.66  fof(f28,plain,(
% 2.22/0.66    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.66    inference(flattening,[],[f27])).
% 2.22/0.66  fof(f27,plain,(
% 2.22/0.66    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.66    inference(ennf_transformation,[],[f5])).
% 2.22/0.66  fof(f5,axiom,(
% 2.22/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 2.22/0.66  fof(f70,plain,(
% 2.22/0.66    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f30])).
% 2.22/0.66  fof(f30,plain,(
% 2.22/0.66    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.66    inference(flattening,[],[f29])).
% 2.22/0.66  fof(f29,plain,(
% 2.22/0.66    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.66    inference(ennf_transformation,[],[f6])).
% 2.22/0.66  fof(f6,axiom,(
% 2.22/0.66    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 2.22/0.66  fof(f599,plain,(
% 2.22/0.66    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1)) | k4_relat_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0)) )),
% 2.22/0.66    inference(subsumption_resolution,[],[f597,f191])).
% 2.22/0.66  fof(f191,plain,(
% 2.22/0.66    ( ! [X1] : (v1_funct_1(k4_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.22/0.66    inference(duplicate_literal_removal,[],[f188])).
% 2.22/0.66  fof(f188,plain,(
% 2.22/0.66    ( ! [X1] : (v1_funct_1(k4_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.22/0.66    inference(superposition,[],[f71,f69])).
% 2.22/0.66  fof(f71,plain,(
% 2.22/0.66    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f30])).
% 2.22/0.66  fof(f597,plain,(
% 2.22/0.66    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1)) | k4_relat_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0)) )),
% 2.22/0.66    inference(duplicate_literal_removal,[],[f592])).
% 2.22/0.66  fof(f592,plain,(
% 2.22/0.66    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1)) | k4_relat_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(superposition,[],[f338,f217])).
% 2.22/0.66  fof(f217,plain,(
% 2.22/0.66    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k4_relat_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(duplicate_literal_removal,[],[f216])).
% 2.22/0.66  fof(f216,plain,(
% 2.22/0.66    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k4_relat_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(superposition,[],[f68,f69])).
% 2.22/0.66  fof(f68,plain,(
% 2.22/0.66    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f26])).
% 2.22/0.66  fof(f26,plain,(
% 2.22/0.66    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.22/0.66    inference(flattening,[],[f25])).
% 2.22/0.66  fof(f25,plain,(
% 2.22/0.66    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.22/0.66    inference(ennf_transformation,[],[f8])).
% 2.22/0.66  fof(f8,axiom,(
% 2.22/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 2.22/0.66  fof(f338,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (k6_relat_1(k1_relat_1(X2)) != k5_relat_1(k4_relat_1(X0),X1) | k4_relat_1(X0) = X2 | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(superposition,[],[f99,f86])).
% 2.22/0.66  fof(f86,plain,(
% 2.22/0.66    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f39])).
% 2.22/0.66  fof(f39,plain,(
% 2.22/0.66    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.22/0.66    inference(ennf_transformation,[],[f4])).
% 2.22/0.66  fof(f4,axiom,(
% 2.22/0.66    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 2.22/0.66  fof(f99,plain,(
% 2.22/0.66    ( ! [X2,X3,X1] : (k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1)) | X1 = X3 | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.22/0.66    inference(equality_resolution,[],[f84])).
% 2.22/0.66  fof(f84,plain,(
% 2.22/0.66    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f38])).
% 2.22/0.66  fof(f38,plain,(
% 2.22/0.66    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.22/0.66    inference(flattening,[],[f37])).
% 2.22/0.66  fof(f37,plain,(
% 2.22/0.66    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.22/0.66    inference(ennf_transformation,[],[f7])).
% 2.22/0.66  fof(f7,axiom,(
% 2.22/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).
% 2.22/0.66  fof(f607,plain,(
% 2.22/0.66    ~spl4_7 | ~spl4_10 | spl4_43),
% 2.22/0.66    inference(avatar_contradiction_clause,[],[f605])).
% 2.22/0.66  fof(f605,plain,(
% 2.22/0.66    $false | (~spl4_7 | ~spl4_10 | spl4_43)),
% 2.22/0.66    inference(unit_resulting_resolution,[],[f149,f134,f488,f293])).
% 2.22/0.66  fof(f293,plain,(
% 2.22/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.66    inference(duplicate_literal_removal,[],[f292])).
% 2.22/0.66  fof(f292,plain,(
% 2.22/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.66    inference(superposition,[],[f88,f89])).
% 2.22/0.66  fof(f89,plain,(
% 2.22/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.66    inference(cnf_transformation,[],[f44])).
% 2.22/0.66  fof(f44,plain,(
% 2.22/0.66    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(flattening,[],[f43])).
% 2.22/0.66  fof(f43,plain,(
% 2.22/0.66    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.22/0.66    inference(ennf_transformation,[],[f11])).
% 2.22/0.66  fof(f11,axiom,(
% 2.22/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 2.22/0.66  fof(f88,plain,(
% 2.22/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.66    inference(cnf_transformation,[],[f42])).
% 2.22/0.66  fof(f42,plain,(
% 2.22/0.66    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(flattening,[],[f41])).
% 2.22/0.66  fof(f41,plain,(
% 2.22/0.66    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.22/0.66    inference(ennf_transformation,[],[f9])).
% 2.22/0.66  fof(f9,axiom,(
% 2.22/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 2.22/0.66  fof(f488,plain,(
% 2.22/0.66    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_43),
% 2.22/0.66    inference(avatar_component_clause,[],[f486])).
% 2.22/0.66  fof(f486,plain,(
% 2.22/0.66    spl4_43 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 2.22/0.66  fof(f134,plain,(
% 2.22/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 2.22/0.66    inference(avatar_component_clause,[],[f132])).
% 2.22/0.66  fof(f132,plain,(
% 2.22/0.66    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.22/0.66  fof(f149,plain,(
% 2.22/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 2.22/0.66    inference(avatar_component_clause,[],[f147])).
% 2.22/0.66  fof(f147,plain,(
% 2.22/0.66    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.22/0.66  fof(f493,plain,(
% 2.22/0.66    ~spl4_43 | spl4_44 | ~spl4_29),
% 2.22/0.66    inference(avatar_split_clause,[],[f474,f332,f490,f486])).
% 2.22/0.66  fof(f332,plain,(
% 2.22/0.66    spl4_29 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.22/0.66  fof(f474,plain,(
% 2.22/0.66    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_29),
% 2.22/0.66    inference(resolution,[],[f265,f334])).
% 2.22/0.66  fof(f334,plain,(
% 2.22/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_29),
% 2.22/0.66    inference(avatar_component_clause,[],[f332])).
% 2.22/0.66  fof(f265,plain,(
% 2.22/0.66    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.22/0.66    inference(resolution,[],[f79,f167])).
% 2.22/0.66  fof(f167,plain,(
% 2.22/0.66    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.22/0.66    inference(forward_demodulation,[],[f81,f82])).
% 2.22/0.66  fof(f82,plain,(
% 2.22/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f16])).
% 2.22/0.66  fof(f16,axiom,(
% 2.22/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.22/0.66  fof(f81,plain,(
% 2.22/0.66    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.22/0.66    inference(cnf_transformation,[],[f20])).
% 2.22/0.66  fof(f20,plain,(
% 2.22/0.66    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.22/0.66    inference(pure_predicate_removal,[],[f14])).
% 2.22/0.66  fof(f14,axiom,(
% 2.22/0.66    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.22/0.66  fof(f79,plain,(
% 2.22/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.66    inference(cnf_transformation,[],[f51])).
% 2.22/0.66  fof(f51,plain,(
% 2.22/0.66    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(nnf_transformation,[],[f34])).
% 2.22/0.66  fof(f34,plain,(
% 2.22/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(flattening,[],[f33])).
% 2.22/0.66  fof(f33,plain,(
% 2.22/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.22/0.66    inference(ennf_transformation,[],[f12])).
% 2.22/0.66  fof(f12,axiom,(
% 2.22/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.22/0.66  fof(f472,plain,(
% 2.22/0.66    spl4_40 | ~spl4_15 | ~spl4_39),
% 2.22/0.66    inference(avatar_split_clause,[],[f471,f447,f181,f467])).
% 2.22/0.66  fof(f447,plain,(
% 2.22/0.66    spl4_39 <=> sK1 = k1_relat_1(k4_relat_1(sK2))),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.22/0.66  fof(f471,plain,(
% 2.22/0.66    sK1 = k2_relat_1(sK2) | (~spl4_15 | ~spl4_39)),
% 2.22/0.66    inference(subsumption_resolution,[],[f463,f183])).
% 2.22/0.66  fof(f463,plain,(
% 2.22/0.66    sK1 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl4_39),
% 2.22/0.66    inference(superposition,[],[f85,f449])).
% 2.22/0.66  fof(f449,plain,(
% 2.22/0.66    sK1 = k1_relat_1(k4_relat_1(sK2)) | ~spl4_39),
% 2.22/0.66    inference(avatar_component_clause,[],[f447])).
% 2.22/0.66  fof(f85,plain,(
% 2.22/0.66    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f39])).
% 2.22/0.66  fof(f450,plain,(
% 2.22/0.66    spl4_39 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_38),
% 2.22/0.66    inference(avatar_split_clause,[],[f445,f431,f181,f157,f117,f447])).
% 2.22/0.66  fof(f431,plain,(
% 2.22/0.66    spl4_38 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 2.22/0.66  fof(f445,plain,(
% 2.22/0.66    sK1 = k1_relat_1(k4_relat_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_38)),
% 2.22/0.66    inference(subsumption_resolution,[],[f444,f183])).
% 2.22/0.66  fof(f444,plain,(
% 2.22/0.66    sK1 = k1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_38)),
% 2.22/0.66    inference(subsumption_resolution,[],[f443,f159])).
% 2.22/0.66  fof(f443,plain,(
% 2.22/0.66    sK1 = k1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_38)),
% 2.22/0.66    inference(subsumption_resolution,[],[f442,f119])).
% 2.22/0.66  fof(f442,plain,(
% 2.22/0.66    sK1 = k1_relat_1(k4_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_38),
% 2.22/0.66    inference(superposition,[],[f433,f69])).
% 2.22/0.66  fof(f433,plain,(
% 2.22/0.66    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_38),
% 2.22/0.66    inference(avatar_component_clause,[],[f431])).
% 2.22/0.66  fof(f436,plain,(
% 2.22/0.66    spl4_38 | ~spl4_28 | ~spl4_31),
% 2.22/0.66    inference(avatar_split_clause,[],[f435,f365,f322,f431])).
% 2.22/0.66  fof(f322,plain,(
% 2.22/0.66    spl4_28 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 2.22/0.66  fof(f365,plain,(
% 2.22/0.66    spl4_31 <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 2.22/0.66  fof(f435,plain,(
% 2.22/0.66    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl4_28 | ~spl4_31)),
% 2.22/0.66    inference(subsumption_resolution,[],[f419,f324])).
% 2.22/0.66  fof(f324,plain,(
% 2.22/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_28),
% 2.22/0.66    inference(avatar_component_clause,[],[f322])).
% 2.22/0.66  fof(f419,plain,(
% 2.22/0.66    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_31),
% 2.22/0.66    inference(superposition,[],[f90,f367])).
% 2.22/0.66  fof(f367,plain,(
% 2.22/0.66    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~spl4_31),
% 2.22/0.66    inference(avatar_component_clause,[],[f365])).
% 2.22/0.66  fof(f90,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.22/0.66    inference(cnf_transformation,[],[f45])).
% 2.22/0.66  fof(f45,plain,(
% 2.22/0.66    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(ennf_transformation,[],[f10])).
% 2.22/0.66  fof(f10,axiom,(
% 2.22/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.22/0.66  fof(f368,plain,(
% 2.22/0.66    spl4_31 | spl4_3 | ~spl4_26 | ~spl4_28),
% 2.22/0.66    inference(avatar_split_clause,[],[f363,f322,f302,f112,f365])).
% 2.22/0.66  fof(f112,plain,(
% 2.22/0.66    spl4_3 <=> k1_xboole_0 = sK0),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.22/0.66  fof(f302,plain,(
% 2.22/0.66    spl4_26 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.22/0.66  fof(f363,plain,(
% 2.22/0.66    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | (spl4_3 | ~spl4_26 | ~spl4_28)),
% 2.22/0.66    inference(subsumption_resolution,[],[f362,f114])).
% 2.22/0.66  fof(f114,plain,(
% 2.22/0.66    k1_xboole_0 != sK0 | spl4_3),
% 2.22/0.66    inference(avatar_component_clause,[],[f112])).
% 2.22/0.66  fof(f362,plain,(
% 2.22/0.66    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_26 | ~spl4_28)),
% 2.22/0.66    inference(subsumption_resolution,[],[f358,f304])).
% 2.22/0.66  fof(f304,plain,(
% 2.22/0.66    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl4_26),
% 2.22/0.66    inference(avatar_component_clause,[],[f302])).
% 2.22/0.66  fof(f358,plain,(
% 2.22/0.66    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~spl4_28),
% 2.22/0.66    inference(resolution,[],[f324,f73])).
% 2.22/0.66  fof(f73,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.22/0.66    inference(cnf_transformation,[],[f50])).
% 2.22/0.66  fof(f50,plain,(
% 2.22/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(nnf_transformation,[],[f32])).
% 2.22/0.66  fof(f32,plain,(
% 2.22/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(flattening,[],[f31])).
% 2.22/0.66  fof(f31,plain,(
% 2.22/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.22/0.66    inference(ennf_transformation,[],[f13])).
% 2.22/0.66  fof(f13,axiom,(
% 2.22/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.22/0.66  fof(f356,plain,(
% 2.22/0.66    spl4_30 | ~spl4_10 | ~spl4_22),
% 2.22/0.66    inference(avatar_split_clause,[],[f355,f245,f147,f351])).
% 2.22/0.66  fof(f245,plain,(
% 2.22/0.66    spl4_22 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.22/0.66  fof(f355,plain,(
% 2.22/0.66    sK0 = k1_relat_1(sK2) | (~spl4_10 | ~spl4_22)),
% 2.22/0.66    inference(subsumption_resolution,[],[f347,f149])).
% 2.22/0.66  fof(f347,plain,(
% 2.22/0.66    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_22),
% 2.22/0.66    inference(superposition,[],[f90,f247])).
% 2.22/0.66  fof(f247,plain,(
% 2.22/0.66    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_22),
% 2.22/0.66    inference(avatar_component_clause,[],[f245])).
% 2.22/0.66  fof(f335,plain,(
% 2.22/0.66    spl4_29 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 2.22/0.66    inference(avatar_split_clause,[],[f330,f163,f157,f147,f142,f132,f332])).
% 2.22/0.66  fof(f163,plain,(
% 2.22/0.66    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.22/0.66  fof(f330,plain,(
% 2.22/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 2.22/0.66    inference(subsumption_resolution,[],[f329,f159])).
% 2.22/0.66  fof(f329,plain,(
% 2.22/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 2.22/0.66    inference(subsumption_resolution,[],[f328,f149])).
% 2.22/0.66  fof(f328,plain,(
% 2.22/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 2.22/0.66    inference(subsumption_resolution,[],[f327,f144])).
% 2.22/0.66  fof(f327,plain,(
% 2.22/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 2.22/0.66    inference(subsumption_resolution,[],[f326,f134])).
% 2.22/0.66  fof(f326,plain,(
% 2.22/0.66    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 2.22/0.66    inference(superposition,[],[f165,f83])).
% 2.22/0.66  fof(f83,plain,(
% 2.22/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f36])).
% 2.22/0.66  fof(f36,plain,(
% 2.22/0.66    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.22/0.66    inference(flattening,[],[f35])).
% 2.22/0.66  fof(f35,plain,(
% 2.22/0.66    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.22/0.66    inference(ennf_transformation,[],[f15])).
% 2.22/0.66  fof(f15,axiom,(
% 2.22/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.22/0.66  fof(f165,plain,(
% 2.22/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 2.22/0.66    inference(avatar_component_clause,[],[f163])).
% 2.22/0.66  fof(f325,plain,(
% 2.22/0.66    spl4_28 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.22/0.66    inference(avatar_split_clause,[],[f320,f157,f152,f147,f127,f117,f322])).
% 2.22/0.66  fof(f127,plain,(
% 2.22/0.66    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.22/0.66  fof(f152,plain,(
% 2.22/0.66    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.22/0.66  fof(f320,plain,(
% 2.22/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.22/0.66    inference(subsumption_resolution,[],[f319,f159])).
% 2.22/0.66  fof(f319,plain,(
% 2.22/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.22/0.66    inference(subsumption_resolution,[],[f318,f154])).
% 2.22/0.66  fof(f154,plain,(
% 2.22/0.66    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 2.22/0.66    inference(avatar_component_clause,[],[f152])).
% 2.22/0.66  fof(f318,plain,(
% 2.22/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.22/0.66    inference(subsumption_resolution,[],[f317,f149])).
% 2.22/0.66  fof(f317,plain,(
% 2.22/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 2.22/0.66    inference(subsumption_resolution,[],[f316,f119])).
% 2.22/0.66  fof(f316,plain,(
% 2.22/0.66    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.22/0.66    inference(trivial_inequality_removal,[],[f315])).
% 2.22/0.66  fof(f315,plain,(
% 2.22/0.66    sK1 != sK1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.22/0.66    inference(superposition,[],[f66,f129])).
% 2.22/0.66  fof(f129,plain,(
% 2.22/0.66    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 2.22/0.66    inference(avatar_component_clause,[],[f127])).
% 2.22/0.66  fof(f66,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f24])).
% 2.22/0.66  fof(f24,plain,(
% 2.22/0.66    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.22/0.66    inference(flattening,[],[f23])).
% 2.22/0.66  fof(f23,plain,(
% 2.22/0.66    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.22/0.66    inference(ennf_transformation,[],[f17])).
% 2.22/0.66  fof(f17,axiom,(
% 2.22/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.22/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 2.22/0.66  fof(f305,plain,(
% 2.22/0.66    spl4_26 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 2.22/0.66    inference(avatar_split_clause,[],[f300,f157,f152,f147,f127,f117,f302])).
% 2.22/0.66  fof(f300,plain,(
% 2.22/0.66    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 2.22/0.66    inference(subsumption_resolution,[],[f299,f159])).
% 2.22/0.66  fof(f299,plain,(
% 2.22/0.66    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 2.22/0.66    inference(subsumption_resolution,[],[f298,f154])).
% 2.22/0.66  fof(f298,plain,(
% 2.22/0.66    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_10)),
% 2.22/0.66    inference(subsumption_resolution,[],[f297,f149])).
% 2.22/0.66  fof(f297,plain,(
% 2.22/0.66    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6)),
% 2.22/0.66    inference(subsumption_resolution,[],[f296,f119])).
% 2.22/0.66  fof(f296,plain,(
% 2.22/0.66    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.22/0.66    inference(trivial_inequality_removal,[],[f295])).
% 2.22/0.66  fof(f295,plain,(
% 2.22/0.66    sK1 != sK1 | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 2.22/0.66    inference(superposition,[],[f65,f129])).
% 2.22/0.66  fof(f65,plain,(
% 2.22/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.22/0.66    inference(cnf_transformation,[],[f24])).
% 2.22/0.66  fof(f258,plain,(
% 2.22/0.66    spl4_23 | ~spl4_7 | ~spl4_21),
% 2.22/0.66    inference(avatar_split_clause,[],[f257,f238,f132,f253])).
% 2.22/0.66  fof(f238,plain,(
% 2.22/0.66    spl4_21 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.22/0.66  fof(f257,plain,(
% 2.22/0.66    sK1 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_21)),
% 2.22/0.66    inference(subsumption_resolution,[],[f250,f134])).
% 2.22/0.66  fof(f250,plain,(
% 2.22/0.66    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_21),
% 2.22/0.66    inference(superposition,[],[f90,f240])).
% 2.22/0.66  fof(f240,plain,(
% 2.22/0.66    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_21),
% 2.22/0.66    inference(avatar_component_clause,[],[f238])).
% 2.22/0.66  fof(f248,plain,(
% 2.22/0.66    spl4_22 | spl4_2 | ~spl4_10 | ~spl4_11),
% 2.22/0.66    inference(avatar_split_clause,[],[f243,f152,f147,f107,f245])).
% 2.22/0.66  fof(f107,plain,(
% 2.22/0.66    spl4_2 <=> k1_xboole_0 = sK1),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.22/0.66  fof(f243,plain,(
% 2.22/0.66    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.22/0.66    inference(subsumption_resolution,[],[f242,f109])).
% 2.22/0.66  fof(f109,plain,(
% 2.22/0.66    k1_xboole_0 != sK1 | spl4_2),
% 2.22/0.66    inference(avatar_component_clause,[],[f107])).
% 2.22/0.66  fof(f242,plain,(
% 2.22/0.66    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_10 | ~spl4_11)),
% 2.22/0.66    inference(subsumption_resolution,[],[f233,f154])).
% 2.22/0.66  fof(f233,plain,(
% 2.22/0.66    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_10),
% 2.22/0.66    inference(resolution,[],[f73,f149])).
% 2.22/0.66  fof(f241,plain,(
% 2.22/0.66    spl4_21 | spl4_3 | ~spl4_7 | ~spl4_8),
% 2.22/0.66    inference(avatar_split_clause,[],[f236,f137,f132,f112,f238])).
% 2.22/0.66  fof(f137,plain,(
% 2.22/0.66    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.22/0.66  fof(f236,plain,(
% 2.22/0.66    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_3 | ~spl4_7 | ~spl4_8)),
% 2.22/0.66    inference(subsumption_resolution,[],[f235,f114])).
% 2.22/0.66  fof(f235,plain,(
% 2.22/0.66    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8)),
% 2.22/0.66    inference(subsumption_resolution,[],[f232,f139])).
% 2.22/0.66  fof(f139,plain,(
% 2.22/0.66    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 2.22/0.66    inference(avatar_component_clause,[],[f137])).
% 2.22/0.66  fof(f232,plain,(
% 2.22/0.66    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_7),
% 2.22/0.66    inference(resolution,[],[f73,f134])).
% 2.22/0.66  fof(f200,plain,(
% 2.22/0.66    ~spl4_16 | spl4_1 | ~spl4_4 | ~spl4_12 | ~spl4_15),
% 2.22/0.66    inference(avatar_split_clause,[],[f195,f181,f157,f117,f102,f197])).
% 2.22/0.66  fof(f102,plain,(
% 2.22/0.66    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 2.22/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.22/0.66  fof(f195,plain,(
% 2.22/0.66    sK3 != k4_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_12 | ~spl4_15)),
% 2.22/0.66    inference(subsumption_resolution,[],[f194,f183])).
% 2.22/0.66  fof(f194,plain,(
% 2.22/0.66    sK3 != k4_relat_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_12)),
% 2.22/0.66    inference(subsumption_resolution,[],[f193,f159])).
% 2.22/0.66  fof(f193,plain,(
% 2.22/0.66    sK3 != k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4)),
% 2.22/0.66    inference(subsumption_resolution,[],[f186,f119])).
% 2.22/0.66  fof(f186,plain,(
% 2.22/0.66    sK3 != k4_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 2.22/0.66    inference(superposition,[],[f104,f69])).
% 2.22/0.66  fof(f104,plain,(
% 2.22/0.66    k2_funct_1(sK2) != sK3 | spl4_1),
% 2.22/0.66    inference(avatar_component_clause,[],[f102])).
% 2.22/0.66  fof(f184,plain,(
% 2.22/0.66    spl4_15 | ~spl4_10),
% 2.22/0.66    inference(avatar_split_clause,[],[f179,f147,f181])).
% 2.22/0.67  fof(f179,plain,(
% 2.22/0.67    v1_relat_1(sK2) | ~spl4_10),
% 2.22/0.67    inference(subsumption_resolution,[],[f171,f92])).
% 2.22/0.67  fof(f92,plain,(
% 2.22/0.67    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.22/0.67    inference(cnf_transformation,[],[f2])).
% 2.22/0.67  fof(f2,axiom,(
% 2.22/0.67    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.22/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.22/0.67  fof(f171,plain,(
% 2.22/0.67    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 2.22/0.67    inference(resolution,[],[f91,f149])).
% 2.22/0.67  fof(f91,plain,(
% 2.22/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.22/0.67    inference(cnf_transformation,[],[f46])).
% 2.22/0.67  fof(f46,plain,(
% 2.22/0.67    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.22/0.67    inference(ennf_transformation,[],[f1])).
% 2.22/0.67  fof(f1,axiom,(
% 2.22/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.22/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.22/0.67  fof(f178,plain,(
% 2.22/0.67    spl4_14 | ~spl4_7),
% 2.22/0.67    inference(avatar_split_clause,[],[f173,f132,f175])).
% 2.22/0.67  fof(f173,plain,(
% 2.22/0.67    v1_relat_1(sK3) | ~spl4_7),
% 2.22/0.67    inference(subsumption_resolution,[],[f170,f92])).
% 2.22/0.67  fof(f170,plain,(
% 2.22/0.67    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 2.22/0.67    inference(resolution,[],[f91,f134])).
% 2.22/0.67  fof(f166,plain,(
% 2.22/0.67    spl4_13 | ~spl4_5),
% 2.22/0.67    inference(avatar_split_clause,[],[f161,f122,f163])).
% 2.22/0.67  fof(f122,plain,(
% 2.22/0.67    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.22/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.22/0.67  fof(f161,plain,(
% 2.22/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 2.22/0.67    inference(backward_demodulation,[],[f124,f82])).
% 2.22/0.67  fof(f124,plain,(
% 2.22/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 2.22/0.67    inference(avatar_component_clause,[],[f122])).
% 2.22/0.67  fof(f160,plain,(
% 2.22/0.67    spl4_12),
% 2.22/0.67    inference(avatar_split_clause,[],[f52,f157])).
% 2.22/0.67  fof(f52,plain,(
% 2.22/0.67    v1_funct_1(sK2)),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f49,plain,(
% 2.22/0.67    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.22/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f48,f47])).
% 2.22/0.67  fof(f47,plain,(
% 2.22/0.67    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.22/0.67    introduced(choice_axiom,[])).
% 2.22/0.67  fof(f48,plain,(
% 2.22/0.67    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.22/0.67    introduced(choice_axiom,[])).
% 2.22/0.67  fof(f22,plain,(
% 2.22/0.67    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.22/0.67    inference(flattening,[],[f21])).
% 2.22/0.67  fof(f21,plain,(
% 2.22/0.67    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.22/0.67    inference(ennf_transformation,[],[f19])).
% 2.22/0.67  fof(f19,negated_conjecture,(
% 2.22/0.67    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.22/0.67    inference(negated_conjecture,[],[f18])).
% 2.22/0.67  fof(f18,conjecture,(
% 2.22/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.22/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.22/0.67  fof(f155,plain,(
% 2.22/0.67    spl4_11),
% 2.22/0.67    inference(avatar_split_clause,[],[f53,f152])).
% 2.22/0.67  fof(f53,plain,(
% 2.22/0.67    v1_funct_2(sK2,sK0,sK1)),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f150,plain,(
% 2.22/0.67    spl4_10),
% 2.22/0.67    inference(avatar_split_clause,[],[f54,f147])).
% 2.22/0.67  fof(f54,plain,(
% 2.22/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f145,plain,(
% 2.22/0.67    spl4_9),
% 2.22/0.67    inference(avatar_split_clause,[],[f55,f142])).
% 2.22/0.67  fof(f55,plain,(
% 2.22/0.67    v1_funct_1(sK3)),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f140,plain,(
% 2.22/0.67    spl4_8),
% 2.22/0.67    inference(avatar_split_clause,[],[f56,f137])).
% 2.22/0.67  fof(f56,plain,(
% 2.22/0.67    v1_funct_2(sK3,sK1,sK0)),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f135,plain,(
% 2.22/0.67    spl4_7),
% 2.22/0.67    inference(avatar_split_clause,[],[f57,f132])).
% 2.22/0.67  fof(f57,plain,(
% 2.22/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f130,plain,(
% 2.22/0.67    spl4_6),
% 2.22/0.67    inference(avatar_split_clause,[],[f58,f127])).
% 2.22/0.67  fof(f58,plain,(
% 2.22/0.67    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f125,plain,(
% 2.22/0.67    spl4_5),
% 2.22/0.67    inference(avatar_split_clause,[],[f59,f122])).
% 2.22/0.67  fof(f59,plain,(
% 2.22/0.67    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f120,plain,(
% 2.22/0.67    spl4_4),
% 2.22/0.67    inference(avatar_split_clause,[],[f60,f117])).
% 2.22/0.67  fof(f60,plain,(
% 2.22/0.67    v2_funct_1(sK2)),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f115,plain,(
% 2.22/0.67    ~spl4_3),
% 2.22/0.67    inference(avatar_split_clause,[],[f61,f112])).
% 2.22/0.67  fof(f61,plain,(
% 2.22/0.67    k1_xboole_0 != sK0),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f110,plain,(
% 2.22/0.67    ~spl4_2),
% 2.22/0.67    inference(avatar_split_clause,[],[f62,f107])).
% 2.22/0.67  fof(f62,plain,(
% 2.22/0.67    k1_xboole_0 != sK1),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  fof(f105,plain,(
% 2.22/0.67    ~spl4_1),
% 2.22/0.67    inference(avatar_split_clause,[],[f63,f102])).
% 2.22/0.67  fof(f63,plain,(
% 2.22/0.67    k2_funct_1(sK2) != sK3),
% 2.22/0.67    inference(cnf_transformation,[],[f49])).
% 2.22/0.67  % SZS output end Proof for theBenchmark
% 2.22/0.67  % (25457)------------------------------
% 2.22/0.67  % (25457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.67  % (25457)Termination reason: Refutation
% 2.22/0.67  
% 2.22/0.67  % (25457)Memory used [KB]: 7291
% 2.22/0.67  % (25457)Time elapsed: 0.236 s
% 2.22/0.67  % (25457)------------------------------
% 2.22/0.67  % (25457)------------------------------
% 2.22/0.67  % (25435)Success in time 0.302 s
%------------------------------------------------------------------------------
