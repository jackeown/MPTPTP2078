%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:54 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  233 ( 456 expanded)
%              Number of leaves         :   53 ( 171 expanded)
%              Depth                    :   12
%              Number of atoms          :  814 (2175 expanded)
%              Number of equality atoms :  171 ( 613 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1556,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f162,f166,f170,f192,f194,f331,f333,f367,f380,f385,f394,f396,f408,f422,f432,f450,f467,f470,f472,f500,f506,f558,f622,f747,f769,f790,f979,f1006,f1027,f1046,f1255,f1503,f1543])).

fof(f1543,plain,(
    ~ spl4_42 ),
    inference(avatar_contradiction_clause,[],[f1511])).

fof(f1511,plain,
    ( $false
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f72,f644])).

fof(f644,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f642])).

fof(f642,plain,
    ( spl4_42
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f72,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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

fof(f1503,plain,
    ( ~ spl4_24
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_1
    | ~ spl4_3
    | spl4_42
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_54
    | ~ spl4_118 ),
    inference(avatar_split_clause,[],[f1502,f1252,f721,f447,f188,f642,f155,f146,f443,f325,f439])).

fof(f439,plain,
    ( spl4_24
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f325,plain,
    ( spl4_13
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f443,plain,
    ( spl4_25
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f146,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f155,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f188,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f447,plain,
    ( spl4_26
  <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f721,plain,
    ( spl4_54
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1252,plain,
    ( spl4_118
  <=> sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f1502,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_54
    | ~ spl4_118 ),
    inference(forward_demodulation,[],[f1501,f449])).

fof(f449,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f447])).

fof(f1501,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_54
    | ~ spl4_118 ),
    inference(forward_demodulation,[],[f1500,f1254])).

fof(f1254,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_118 ),
    inference(avatar_component_clause,[],[f1252])).

fof(f1500,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f1372,f190])).

fof(f190,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f1372,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_54 ),
    inference(superposition,[],[f256,f723])).

fof(f723,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f721])).

fof(f256,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f87,f131])).

fof(f131,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f99,f76])).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1255,plain,
    ( ~ spl4_27
    | ~ spl4_28
    | ~ spl4_1
    | ~ spl4_29
    | spl4_118
    | ~ spl4_22
    | ~ spl4_89
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f1250,f1043,f1003,f418,f1252,f488,f146,f484,f480])).

fof(f480,plain,
    ( spl4_27
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f484,plain,
    ( spl4_28
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f488,plain,
    ( spl4_29
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f418,plain,
    ( spl4_22
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f1003,plain,
    ( spl4_89
  <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f1043,plain,
    ( spl4_96
  <=> sK3 = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f1250,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_22
    | ~ spl4_89
    | ~ spl4_96 ),
    inference(forward_demodulation,[],[f1249,f420])).

fof(f420,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f418])).

fof(f1249,plain,
    ( sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_89
    | ~ spl4_96 ),
    inference(forward_demodulation,[],[f1219,f1045])).

fof(f1045,plain,
    ( sK3 = k5_relat_1(sK3,k6_partfun1(sK0))
    | ~ spl4_96 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1219,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = k5_relat_1(sK3,k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_89 ),
    inference(duplicate_literal_removal,[],[f1207])).

fof(f1207,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = k5_relat_1(sK3,k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_89 ),
    inference(superposition,[],[f254,f1005])).

fof(f1005,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ spl4_89 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f254,plain,(
    ! [X6,X7] :
      ( k5_relat_1(X6,k5_relat_1(k2_funct_1(X6),X7)) = k5_relat_1(k6_partfun1(k1_relat_1(X6)),X7)
      | ~ v1_relat_1(k2_funct_1(X6))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v2_funct_1(X6) ) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,(
    ! [X6,X7] :
      ( k5_relat_1(X6,k5_relat_1(k2_funct_1(X6),X7)) = k5_relat_1(k6_partfun1(k1_relat_1(X6)),X7)
      | ~ v1_relat_1(k2_funct_1(X6))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v2_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f87,f132])).

fof(f132,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f98,f76])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1046,plain,
    ( ~ spl4_1
    | spl4_96
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f1033,f998,f1043,f146])).

fof(f998,plain,
    ( spl4_88
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f1033,plain,
    ( sK3 = k5_relat_1(sK3,k6_partfun1(sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_88 ),
    inference(superposition,[],[f130,f1000])).

fof(f1000,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f998])).

fof(f130,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f86,f76])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f1027,plain,
    ( ~ spl4_21
    | spl4_88
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f991,f976,f998,f414])).

fof(f414,plain,
    ( spl4_21
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f976,plain,
    ( spl4_86
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f991,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_86 ),
    inference(superposition,[],[f105,f978])).

fof(f978,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f976])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f1006,plain,
    ( spl4_89
    | spl4_17
    | ~ spl4_27
    | ~ spl4_28
    | ~ spl4_21
    | ~ spl4_15
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f996,f976,f356,f414,f484,f480,f364,f1003])).

fof(f364,plain,
    ( spl4_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f356,plain,
    ( spl4_15
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f996,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ spl4_86 ),
    inference(trivial_inequality_removal,[],[f986])).

fof(f986,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ spl4_86 ),
    inference(superposition,[],[f116,f978])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f979,plain,
    ( spl4_86
    | ~ spl4_28
    | ~ spl4_5
    | ~ spl4_18
    | ~ spl4_13
    | ~ spl4_21
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f971,f356,f414,f325,f369,f184,f484,f976])).

fof(f184,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f369,plain,
    ( spl4_18
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f971,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f117,f68])).

fof(f68,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f790,plain,
    ( spl4_31
    | ~ spl4_54 ),
    inference(avatar_contradiction_clause,[],[f787])).

fof(f787,plain,
    ( $false
    | spl4_31
    | ~ spl4_54 ),
    inference(unit_resulting_resolution,[],[f124,f772])).

fof(f772,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_31
    | ~ spl4_54 ),
    inference(superposition,[],[f499,f723])).

fof(f499,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl4_31
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f124,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f79,f76])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f769,plain,
    ( ~ spl4_13
    | ~ spl4_21
    | ~ spl4_28
    | ~ spl4_5
    | spl4_54
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f766,f555,f721,f184,f484,f414,f325])).

fof(f555,plain,
    ( spl4_37
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f766,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_37 ),
    inference(superposition,[],[f120,f557])).

fof(f557,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f555])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f747,plain,(
    spl4_36 ),
    inference(avatar_contradiction_clause,[],[f735])).

fof(f735,plain,
    ( $false
    | spl4_36 ),
    inference(unit_resulting_resolution,[],[f73,f64,f66,f75,f553,f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f553,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_36 ),
    inference(avatar_component_clause,[],[f551])).

fof(f551,plain,
    ( spl4_36
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f622,plain,
    ( ~ spl4_1
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | ~ spl4_1
    | spl4_29 ),
    inference(unit_resulting_resolution,[],[f148,f64,f490,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f490,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f488])).

fof(f148,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f146])).

fof(f558,plain,
    ( ~ spl4_36
    | spl4_37 ),
    inference(avatar_split_clause,[],[f548,f555,f551])).

fof(f548,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f382,f68])).

fof(f382,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f119,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f506,plain,(
    spl4_28 ),
    inference(avatar_contradiction_clause,[],[f505])).

fof(f505,plain,
    ( $false
    | spl4_28 ),
    inference(subsumption_resolution,[],[f64,f486])).

fof(f486,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f484])).

fof(f500,plain,
    ( ~ spl4_28
    | ~ spl4_31
    | ~ spl4_1
    | spl4_27
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f478,f418,f329,f480,f146,f497,f484])).

fof(f329,plain,
    ( spl4_14
  <=> ! [X8] :
        ( sK1 != k1_relat_1(X8)
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v2_funct_1(k5_relat_1(sK2,X8))
        | ~ v1_funct_1(X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f478,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(trivial_inequality_removal,[],[f475])).

fof(f475,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(superposition,[],[f330,f420])).

fof(f330,plain,
    ( ! [X8] :
        ( sK1 != k1_relat_1(X8)
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v2_funct_1(k5_relat_1(sK2,X8))
        | ~ v1_funct_1(X8) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f329])).

fof(f472,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | spl4_21 ),
    inference(subsumption_resolution,[],[f66,f416])).

fof(f416,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f414])).

fof(f470,plain,
    ( ~ spl4_3
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | ~ spl4_3
    | spl4_25 ),
    inference(unit_resulting_resolution,[],[f157,f73,f445,f92])).

fof(f445,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f443])).

fof(f157,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f155])).

fof(f467,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | spl4_24 ),
    inference(subsumption_resolution,[],[f69,f441])).

fof(f441,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f439])).

fof(f69,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f450,plain,
    ( ~ spl4_3
    | ~ spl4_24
    | ~ spl4_13
    | ~ spl4_25
    | spl4_26
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f433,f428,f447,f443,f325,f439,f155])).

fof(f428,plain,
    ( spl4_23
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f433,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(superposition,[],[f179,f430])).

fof(f430,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f428])).

fof(f179,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f130,f95])).

fof(f95,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f432,plain,
    ( ~ spl4_5
    | spl4_23
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f425,f373,f428,f184])).

fof(f373,plain,
    ( spl4_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f425,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_19 ),
    inference(superposition,[],[f104,f375])).

fof(f375,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f373])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f422,plain,
    ( ~ spl4_21
    | spl4_22
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f411,f360,f418,f414])).

fof(f360,plain,
    ( spl4_16
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f411,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_16 ),
    inference(superposition,[],[f104,f362])).

fof(f362,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f360])).

fof(f408,plain,(
    ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f71,f379])).

fof(f379,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f71,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f396,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f74,f371])).

fof(f371,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f369])).

fof(f74,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f394,plain,(
    ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f70,f366])).

fof(f366,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f364])).

fof(f70,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f385,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f65,f358])).

fof(f358,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f356])).

fof(f65,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f380,plain,
    ( ~ spl4_18
    | spl4_19
    | spl4_20 ),
    inference(avatar_split_clause,[],[f354,f377,f373,f369])).

fof(f354,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f111,f75])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f367,plain,
    ( ~ spl4_15
    | spl4_16
    | spl4_17 ),
    inference(avatar_split_clause,[],[f352,f364,f360,f356])).

fof(f352,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f111,f66])).

fof(f333,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f73,f327])).

fof(f327,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f325])).

fof(f331,plain,
    ( ~ spl4_13
    | ~ spl4_3
    | spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f319,f188,f329,f155,f325])).

fof(f319,plain,
    ( ! [X8] :
        ( sK1 != k1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v2_funct_1(k5_relat_1(sK2,X8))
        | ~ v1_relat_1(X8)
        | v2_funct_1(X8) )
    | ~ spl4_6 ),
    inference(superposition,[],[f102,f190])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f194,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f75,f186])).

fof(f186,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f184])).

fof(f192,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f182,f188,f184])).

fof(f182,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f67,f105])).

fof(f67,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f170,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f103,f161])).

fof(f161,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f103,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f166,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f103,f152])).

fof(f152,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f162,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f143,f159,f155])).

fof(f143,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f88,f75])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f153,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f142,f150,f146])).

fof(f142,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f88,f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:00:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (3537)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.49  % (3527)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.50  % (3518)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (3511)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (3532)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (3536)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (3523)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (3526)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (3512)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (3521)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (3515)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (3531)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (3514)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (3535)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (3533)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (3522)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (3534)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (3544)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (3516)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (3524)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (3541)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (3543)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (3525)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (3539)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (3519)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (3542)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (3529)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (3530)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.47/0.56  % (3530)Refutation not found, incomplete strategy% (3530)------------------------------
% 1.47/0.56  % (3530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (3530)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (3530)Memory used [KB]: 10746
% 1.47/0.56  % (3530)Time elapsed: 0.139 s
% 1.47/0.56  % (3530)------------------------------
% 1.47/0.56  % (3530)------------------------------
% 1.47/0.56  % (3538)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.57  % (3527)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.57  % (3528)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f1556,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f153,f162,f166,f170,f192,f194,f331,f333,f367,f380,f385,f394,f396,f408,f422,f432,f450,f467,f470,f472,f500,f506,f558,f622,f747,f769,f790,f979,f1006,f1027,f1046,f1255,f1503,f1543])).
% 1.47/0.57  fof(f1543,plain,(
% 1.47/0.57    ~spl4_42),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f1511])).
% 1.47/0.57  fof(f1511,plain,(
% 1.47/0.57    $false | ~spl4_42),
% 1.47/0.57    inference(subsumption_resolution,[],[f72,f644])).
% 1.47/0.57  fof(f644,plain,(
% 1.47/0.57    sK3 = k2_funct_1(sK2) | ~spl4_42),
% 1.47/0.57    inference(avatar_component_clause,[],[f642])).
% 1.47/0.57  fof(f642,plain,(
% 1.47/0.57    spl4_42 <=> sK3 = k2_funct_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.47/0.57  fof(f72,plain,(
% 1.47/0.57    sK3 != k2_funct_1(sK2)),
% 1.47/0.57    inference(cnf_transformation,[],[f30])).
% 1.47/0.57  fof(f30,plain,(
% 1.47/0.57    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.47/0.57    inference(flattening,[],[f29])).
% 1.47/0.57  fof(f29,plain,(
% 1.47/0.57    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.47/0.57    inference(ennf_transformation,[],[f28])).
% 1.47/0.57  fof(f28,negated_conjecture,(
% 1.47/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.47/0.57    inference(negated_conjecture,[],[f27])).
% 1.47/0.57  fof(f27,conjecture,(
% 1.47/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.47/0.57  fof(f1503,plain,(
% 1.47/0.57    ~spl4_24 | ~spl4_13 | ~spl4_25 | ~spl4_1 | ~spl4_3 | spl4_42 | ~spl4_6 | ~spl4_26 | ~spl4_54 | ~spl4_118),
% 1.47/0.57    inference(avatar_split_clause,[],[f1502,f1252,f721,f447,f188,f642,f155,f146,f443,f325,f439])).
% 1.47/0.57  fof(f439,plain,(
% 1.47/0.57    spl4_24 <=> v2_funct_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.47/0.57  fof(f325,plain,(
% 1.47/0.57    spl4_13 <=> v1_funct_1(sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.47/0.58  fof(f443,plain,(
% 1.47/0.58    spl4_25 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.47/0.58  fof(f146,plain,(
% 1.47/0.58    spl4_1 <=> v1_relat_1(sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.47/0.58  fof(f155,plain,(
% 1.47/0.58    spl4_3 <=> v1_relat_1(sK2)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.47/0.58  fof(f188,plain,(
% 1.47/0.58    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.47/0.58  fof(f447,plain,(
% 1.47/0.58    spl4_26 <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.47/0.58  fof(f721,plain,(
% 1.47/0.58    spl4_54 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 1.47/0.58  fof(f1252,plain,(
% 1.47/0.58    spl4_118 <=> sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).
% 1.47/0.58  fof(f1502,plain,(
% 1.47/0.58    sK3 = k2_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_26 | ~spl4_54 | ~spl4_118)),
% 1.47/0.58    inference(forward_demodulation,[],[f1501,f449])).
% 1.47/0.58  fof(f449,plain,(
% 1.47/0.58    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_26),
% 1.47/0.58    inference(avatar_component_clause,[],[f447])).
% 1.47/0.58  fof(f1501,plain,(
% 1.47/0.58    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_54 | ~spl4_118)),
% 1.47/0.58    inference(forward_demodulation,[],[f1500,f1254])).
% 1.47/0.58  fof(f1254,plain,(
% 1.47/0.58    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_118),
% 1.47/0.58    inference(avatar_component_clause,[],[f1252])).
% 1.47/0.58  fof(f1500,plain,(
% 1.47/0.58    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_54)),
% 1.47/0.58    inference(forward_demodulation,[],[f1372,f190])).
% 1.47/0.58  fof(f190,plain,(
% 1.47/0.58    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 1.47/0.58    inference(avatar_component_clause,[],[f188])).
% 1.47/0.58  fof(f1372,plain,(
% 1.47/0.58    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_54),
% 1.47/0.58    inference(superposition,[],[f256,f723])).
% 1.47/0.58  fof(f723,plain,(
% 1.47/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_54),
% 1.47/0.58    inference(avatar_component_clause,[],[f721])).
% 1.47/0.58  fof(f256,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0)) )),
% 1.47/0.58    inference(duplicate_literal_removal,[],[f240])).
% 1.47/0.58  fof(f240,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.58    inference(superposition,[],[f87,f131])).
% 1.47/0.58  fof(f131,plain,(
% 1.47/0.58    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f99,f76])).
% 1.47/0.58  fof(f76,plain,(
% 1.47/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f23])).
% 1.47/0.58  fof(f23,axiom,(
% 1.47/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.47/0.58  fof(f99,plain,(
% 1.47/0.58    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f43])).
% 1.47/0.58  fof(f43,plain,(
% 1.47/0.58    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.47/0.58    inference(flattening,[],[f42])).
% 1.47/0.58  fof(f42,plain,(
% 1.47/0.58    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.47/0.58    inference(ennf_transformation,[],[f13])).
% 1.47/0.58  fof(f13,axiom,(
% 1.47/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.47/0.58  fof(f87,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f32])).
% 1.47/0.58  fof(f32,plain,(
% 1.47/0.58    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.47/0.58    inference(ennf_transformation,[],[f3])).
% 1.47/0.58  fof(f3,axiom,(
% 1.47/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.47/0.58  fof(f1255,plain,(
% 1.47/0.58    ~spl4_27 | ~spl4_28 | ~spl4_1 | ~spl4_29 | spl4_118 | ~spl4_22 | ~spl4_89 | ~spl4_96),
% 1.47/0.58    inference(avatar_split_clause,[],[f1250,f1043,f1003,f418,f1252,f488,f146,f484,f480])).
% 1.47/0.58  fof(f480,plain,(
% 1.47/0.58    spl4_27 <=> v2_funct_1(sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.47/0.58  fof(f484,plain,(
% 1.47/0.58    spl4_28 <=> v1_funct_1(sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.47/0.58  fof(f488,plain,(
% 1.47/0.58    spl4_29 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.47/0.58  fof(f418,plain,(
% 1.47/0.58    spl4_22 <=> sK1 = k1_relat_1(sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.47/0.58  fof(f1003,plain,(
% 1.47/0.58    spl4_89 <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).
% 1.47/0.58  fof(f1043,plain,(
% 1.47/0.58    spl4_96 <=> sK3 = k5_relat_1(sK3,k6_partfun1(sK0))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 1.47/0.58  fof(f1250,plain,(
% 1.47/0.58    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_22 | ~spl4_89 | ~spl4_96)),
% 1.47/0.58    inference(forward_demodulation,[],[f1249,f420])).
% 1.47/0.58  fof(f420,plain,(
% 1.47/0.58    sK1 = k1_relat_1(sK3) | ~spl4_22),
% 1.47/0.58    inference(avatar_component_clause,[],[f418])).
% 1.47/0.58  fof(f1249,plain,(
% 1.47/0.58    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_89 | ~spl4_96)),
% 1.47/0.58    inference(forward_demodulation,[],[f1219,f1045])).
% 1.47/0.58  fof(f1045,plain,(
% 1.47/0.58    sK3 = k5_relat_1(sK3,k6_partfun1(sK0)) | ~spl4_96),
% 1.47/0.58    inference(avatar_component_clause,[],[f1043])).
% 1.47/0.58  fof(f1219,plain,(
% 1.47/0.58    k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~spl4_89),
% 1.47/0.58    inference(duplicate_literal_removal,[],[f1207])).
% 1.47/0.58  fof(f1207,plain,(
% 1.47/0.58    k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~spl4_89),
% 1.47/0.58    inference(superposition,[],[f254,f1005])).
% 1.47/0.58  fof(f1005,plain,(
% 1.47/0.58    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~spl4_89),
% 1.47/0.58    inference(avatar_component_clause,[],[f1003])).
% 1.47/0.58  fof(f254,plain,(
% 1.47/0.58    ( ! [X6,X7] : (k5_relat_1(X6,k5_relat_1(k2_funct_1(X6),X7)) = k5_relat_1(k6_partfun1(k1_relat_1(X6)),X7) | ~v1_relat_1(k2_funct_1(X6)) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | ~v1_funct_1(X6) | ~v2_funct_1(X6)) )),
% 1.47/0.58    inference(duplicate_literal_removal,[],[f242])).
% 1.47/0.58  fof(f242,plain,(
% 1.47/0.58    ( ! [X6,X7] : (k5_relat_1(X6,k5_relat_1(k2_funct_1(X6),X7)) = k5_relat_1(k6_partfun1(k1_relat_1(X6)),X7) | ~v1_relat_1(k2_funct_1(X6)) | ~v1_relat_1(X7) | ~v1_relat_1(X6) | ~v1_funct_1(X6) | ~v2_funct_1(X6) | ~v1_relat_1(X6)) )),
% 1.47/0.58    inference(superposition,[],[f87,f132])).
% 1.47/0.58  fof(f132,plain,(
% 1.47/0.58    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f98,f76])).
% 1.47/0.58  fof(f98,plain,(
% 1.47/0.58    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f43])).
% 1.47/0.58  fof(f1046,plain,(
% 1.47/0.58    ~spl4_1 | spl4_96 | ~spl4_88),
% 1.47/0.58    inference(avatar_split_clause,[],[f1033,f998,f1043,f146])).
% 1.47/0.58  fof(f998,plain,(
% 1.47/0.58    spl4_88 <=> sK0 = k2_relat_1(sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 1.47/0.58  fof(f1033,plain,(
% 1.47/0.58    sK3 = k5_relat_1(sK3,k6_partfun1(sK0)) | ~v1_relat_1(sK3) | ~spl4_88),
% 1.47/0.58    inference(superposition,[],[f130,f1000])).
% 1.47/0.58  fof(f1000,plain,(
% 1.47/0.58    sK0 = k2_relat_1(sK3) | ~spl4_88),
% 1.47/0.58    inference(avatar_component_clause,[],[f998])).
% 1.47/0.58  fof(f130,plain,(
% 1.47/0.58    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f86,f76])).
% 1.47/0.58  fof(f86,plain,(
% 1.47/0.58    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f31])).
% 1.47/0.58  fof(f31,plain,(
% 1.47/0.58    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.47/0.58    inference(ennf_transformation,[],[f5])).
% 1.47/0.58  fof(f5,axiom,(
% 1.47/0.58    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.47/0.58  fof(f1027,plain,(
% 1.47/0.58    ~spl4_21 | spl4_88 | ~spl4_86),
% 1.47/0.58    inference(avatar_split_clause,[],[f991,f976,f998,f414])).
% 1.47/0.58  fof(f414,plain,(
% 1.47/0.58    spl4_21 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.47/0.58  fof(f976,plain,(
% 1.47/0.58    spl4_86 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 1.47/0.58  fof(f991,plain,(
% 1.47/0.58    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_86),
% 1.47/0.58    inference(superposition,[],[f105,f978])).
% 1.47/0.58  fof(f978,plain,(
% 1.47/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_86),
% 1.47/0.58    inference(avatar_component_clause,[],[f976])).
% 1.47/0.58  fof(f105,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f49])).
% 1.47/0.58  fof(f49,plain,(
% 1.47/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.47/0.58    inference(ennf_transformation,[],[f17])).
% 1.47/0.58  fof(f17,axiom,(
% 1.47/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.47/0.58  fof(f1006,plain,(
% 1.47/0.58    spl4_89 | spl4_17 | ~spl4_27 | ~spl4_28 | ~spl4_21 | ~spl4_15 | ~spl4_86),
% 1.47/0.58    inference(avatar_split_clause,[],[f996,f976,f356,f414,f484,f480,f364,f1003])).
% 1.47/0.58  fof(f364,plain,(
% 1.47/0.58    spl4_17 <=> k1_xboole_0 = sK0),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.47/0.58  fof(f356,plain,(
% 1.47/0.58    spl4_15 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.47/0.58  fof(f996,plain,(
% 1.47/0.58    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~spl4_86),
% 1.47/0.58    inference(trivial_inequality_removal,[],[f986])).
% 1.47/0.58  fof(f986,plain,(
% 1.47/0.58    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~spl4_86),
% 1.47/0.58    inference(superposition,[],[f116,f978])).
% 1.47/0.58  fof(f116,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f55])).
% 1.47/0.58  fof(f55,plain,(
% 1.47/0.58    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.47/0.58    inference(flattening,[],[f54])).
% 1.47/0.58  fof(f54,plain,(
% 1.47/0.58    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.47/0.58    inference(ennf_transformation,[],[f26])).
% 1.47/0.58  fof(f26,axiom,(
% 1.47/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.47/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.47/0.58  fof(f979,plain,(
% 1.47/0.58    spl4_86 | ~spl4_28 | ~spl4_5 | ~spl4_18 | ~spl4_13 | ~spl4_21 | ~spl4_15),
% 1.47/0.58    inference(avatar_split_clause,[],[f971,f356,f414,f325,f369,f184,f484,f976])).
% 1.47/0.58  fof(f184,plain,(
% 1.47/0.58    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.47/0.58  fof(f369,plain,(
% 1.47/0.58    spl4_18 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.47/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.47/0.58  fof(f971,plain,(
% 1.47/0.58    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.47/0.58    inference(resolution,[],[f117,f68])).
% 1.47/0.58  fof(f68,plain,(
% 1.47/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.47/0.58    inference(cnf_transformation,[],[f30])).
% 1.47/0.58  fof(f117,plain,(
% 1.47/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.47/0.58    inference(cnf_transformation,[],[f57])).
% 1.47/0.58  fof(f57,plain,(
% 1.47/0.58    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.47/0.58    inference(flattening,[],[f56])).
% 1.47/0.58  fof(f56,plain,(
% 1.47/0.58    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.47/0.58    inference(ennf_transformation,[],[f24])).
% 1.64/0.58  fof(f24,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.64/0.58  fof(f790,plain,(
% 1.64/0.58    spl4_31 | ~spl4_54),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f787])).
% 1.64/0.58  fof(f787,plain,(
% 1.64/0.58    $false | (spl4_31 | ~spl4_54)),
% 1.64/0.58    inference(unit_resulting_resolution,[],[f124,f772])).
% 1.64/0.58  fof(f772,plain,(
% 1.64/0.58    ~v2_funct_1(k6_partfun1(sK0)) | (spl4_31 | ~spl4_54)),
% 1.64/0.58    inference(superposition,[],[f499,f723])).
% 1.64/0.58  fof(f499,plain,(
% 1.64/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_31),
% 1.64/0.58    inference(avatar_component_clause,[],[f497])).
% 1.64/0.58  fof(f497,plain,(
% 1.64/0.58    spl4_31 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.64/0.58  fof(f124,plain,(
% 1.64/0.58    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.64/0.58    inference(definition_unfolding,[],[f79,f76])).
% 1.64/0.58  fof(f79,plain,(
% 1.64/0.58    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,axiom,(
% 1.64/0.58    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.64/0.58  fof(f769,plain,(
% 1.64/0.58    ~spl4_13 | ~spl4_21 | ~spl4_28 | ~spl4_5 | spl4_54 | ~spl4_37),
% 1.64/0.58    inference(avatar_split_clause,[],[f766,f555,f721,f184,f484,f414,f325])).
% 1.64/0.58  fof(f555,plain,(
% 1.64/0.58    spl4_37 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.64/0.58  fof(f766,plain,(
% 1.64/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_37),
% 1.64/0.58    inference(superposition,[],[f120,f557])).
% 1.64/0.58  fof(f557,plain,(
% 1.64/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_37),
% 1.64/0.58    inference(avatar_component_clause,[],[f555])).
% 1.64/0.58  fof(f120,plain,(
% 1.64/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f61])).
% 1.64/0.58  fof(f61,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.64/0.58    inference(flattening,[],[f60])).
% 1.64/0.58  fof(f60,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.64/0.58    inference(ennf_transformation,[],[f22])).
% 1.64/0.58  fof(f22,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.64/0.58  fof(f747,plain,(
% 1.64/0.58    spl4_36),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f735])).
% 1.64/0.58  fof(f735,plain,(
% 1.64/0.58    $false | spl4_36),
% 1.64/0.58    inference(unit_resulting_resolution,[],[f73,f64,f66,f75,f553,f122])).
% 1.64/0.58  fof(f122,plain,(
% 1.64/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f63])).
% 1.64/0.58  fof(f63,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.64/0.58    inference(flattening,[],[f62])).
% 1.64/0.58  fof(f62,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.64/0.58    inference(ennf_transformation,[],[f20])).
% 1.64/0.58  fof(f20,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.64/0.58  fof(f553,plain,(
% 1.64/0.58    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_36),
% 1.64/0.58    inference(avatar_component_clause,[],[f551])).
% 1.64/0.58  fof(f551,plain,(
% 1.64/0.58    spl4_36 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.64/0.58  fof(f75,plain,(
% 1.64/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f66,plain,(
% 1.64/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f64,plain,(
% 1.64/0.58    v1_funct_1(sK3)),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f73,plain,(
% 1.64/0.58    v1_funct_1(sK2)),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f622,plain,(
% 1.64/0.58    ~spl4_1 | spl4_29),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f620])).
% 1.64/0.58  fof(f620,plain,(
% 1.64/0.58    $false | (~spl4_1 | spl4_29)),
% 1.64/0.58    inference(unit_resulting_resolution,[],[f148,f64,f490,f92])).
% 1.64/0.58  fof(f92,plain,(
% 1.64/0.58    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f37])).
% 1.64/0.58  fof(f37,plain,(
% 1.64/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.58    inference(flattening,[],[f36])).
% 1.64/0.58  fof(f36,plain,(
% 1.64/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.64/0.58    inference(ennf_transformation,[],[f6])).
% 1.64/0.58  fof(f6,axiom,(
% 1.64/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.64/0.58  fof(f490,plain,(
% 1.64/0.58    ~v1_relat_1(k2_funct_1(sK3)) | spl4_29),
% 1.64/0.58    inference(avatar_component_clause,[],[f488])).
% 1.64/0.58  fof(f148,plain,(
% 1.64/0.58    v1_relat_1(sK3) | ~spl4_1),
% 1.64/0.58    inference(avatar_component_clause,[],[f146])).
% 1.64/0.58  fof(f558,plain,(
% 1.64/0.58    ~spl4_36 | spl4_37),
% 1.64/0.58    inference(avatar_split_clause,[],[f548,f555,f551])).
% 1.64/0.58  fof(f548,plain,(
% 1.64/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.64/0.58    inference(resolution,[],[f382,f68])).
% 1.64/0.58  fof(f382,plain,(
% 1.64/0.58    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.64/0.58    inference(resolution,[],[f119,f83])).
% 1.64/0.58  fof(f83,plain,(
% 1.64/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f21])).
% 1.64/0.58  fof(f21,axiom,(
% 1.64/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.64/0.58  fof(f119,plain,(
% 1.64/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f59])).
% 1.64/0.58  fof(f59,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.58    inference(flattening,[],[f58])).
% 1.64/0.58  fof(f58,plain,(
% 1.64/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.64/0.58    inference(ennf_transformation,[],[f18])).
% 1.64/0.58  fof(f18,axiom,(
% 1.64/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.64/0.58  fof(f506,plain,(
% 1.64/0.58    spl4_28),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f505])).
% 1.64/0.58  fof(f505,plain,(
% 1.64/0.58    $false | spl4_28),
% 1.64/0.58    inference(subsumption_resolution,[],[f64,f486])).
% 1.64/0.58  fof(f486,plain,(
% 1.64/0.58    ~v1_funct_1(sK3) | spl4_28),
% 1.64/0.58    inference(avatar_component_clause,[],[f484])).
% 1.64/0.58  fof(f500,plain,(
% 1.64/0.58    ~spl4_28 | ~spl4_31 | ~spl4_1 | spl4_27 | ~spl4_14 | ~spl4_22),
% 1.64/0.58    inference(avatar_split_clause,[],[f478,f418,f329,f480,f146,f497,f484])).
% 1.64/0.58  fof(f329,plain,(
% 1.64/0.58    spl4_14 <=> ! [X8] : (sK1 != k1_relat_1(X8) | v2_funct_1(X8) | ~v1_relat_1(X8) | ~v2_funct_1(k5_relat_1(sK2,X8)) | ~v1_funct_1(X8))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.64/0.58  fof(f478,plain,(
% 1.64/0.58    v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | (~spl4_14 | ~spl4_22)),
% 1.64/0.58    inference(trivial_inequality_removal,[],[f475])).
% 1.64/0.58  fof(f475,plain,(
% 1.64/0.58    sK1 != sK1 | v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | (~spl4_14 | ~spl4_22)),
% 1.64/0.58    inference(superposition,[],[f330,f420])).
% 1.64/0.58  fof(f330,plain,(
% 1.64/0.58    ( ! [X8] : (sK1 != k1_relat_1(X8) | v2_funct_1(X8) | ~v1_relat_1(X8) | ~v2_funct_1(k5_relat_1(sK2,X8)) | ~v1_funct_1(X8)) ) | ~spl4_14),
% 1.64/0.58    inference(avatar_component_clause,[],[f329])).
% 1.64/0.58  fof(f472,plain,(
% 1.64/0.58    spl4_21),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f471])).
% 1.64/0.58  fof(f471,plain,(
% 1.64/0.58    $false | spl4_21),
% 1.64/0.58    inference(subsumption_resolution,[],[f66,f416])).
% 1.64/0.58  fof(f416,plain,(
% 1.64/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_21),
% 1.64/0.58    inference(avatar_component_clause,[],[f414])).
% 1.64/0.58  fof(f470,plain,(
% 1.64/0.58    ~spl4_3 | spl4_25),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f468])).
% 1.64/0.58  fof(f468,plain,(
% 1.64/0.58    $false | (~spl4_3 | spl4_25)),
% 1.64/0.58    inference(unit_resulting_resolution,[],[f157,f73,f445,f92])).
% 1.64/0.58  fof(f445,plain,(
% 1.64/0.58    ~v1_relat_1(k2_funct_1(sK2)) | spl4_25),
% 1.64/0.58    inference(avatar_component_clause,[],[f443])).
% 1.64/0.58  fof(f157,plain,(
% 1.64/0.58    v1_relat_1(sK2) | ~spl4_3),
% 1.64/0.58    inference(avatar_component_clause,[],[f155])).
% 1.64/0.58  fof(f467,plain,(
% 1.64/0.58    spl4_24),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f466])).
% 1.64/0.58  fof(f466,plain,(
% 1.64/0.58    $false | spl4_24),
% 1.64/0.58    inference(subsumption_resolution,[],[f69,f441])).
% 1.64/0.58  fof(f441,plain,(
% 1.64/0.58    ~v2_funct_1(sK2) | spl4_24),
% 1.64/0.58    inference(avatar_component_clause,[],[f439])).
% 1.64/0.58  fof(f69,plain,(
% 1.64/0.58    v2_funct_1(sK2)),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f450,plain,(
% 1.64/0.58    ~spl4_3 | ~spl4_24 | ~spl4_13 | ~spl4_25 | spl4_26 | ~spl4_23),
% 1.64/0.58    inference(avatar_split_clause,[],[f433,f428,f447,f443,f325,f439,f155])).
% 1.64/0.58  fof(f428,plain,(
% 1.64/0.58    spl4_23 <=> sK0 = k1_relat_1(sK2)),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.64/0.58  fof(f433,plain,(
% 1.64/0.58    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_23),
% 1.64/0.58    inference(superposition,[],[f179,f430])).
% 1.64/0.58  fof(f430,plain,(
% 1.64/0.58    sK0 = k1_relat_1(sK2) | ~spl4_23),
% 1.64/0.58    inference(avatar_component_clause,[],[f428])).
% 1.64/0.58  fof(f179,plain,(
% 1.64/0.58    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(superposition,[],[f130,f95])).
% 1.64/0.58  fof(f95,plain,(
% 1.64/0.58    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f39])).
% 1.64/0.58  fof(f39,plain,(
% 1.64/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.58    inference(flattening,[],[f38])).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.64/0.58    inference(ennf_transformation,[],[f11])).
% 1.64/0.58  fof(f11,axiom,(
% 1.64/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.64/0.58  fof(f432,plain,(
% 1.64/0.58    ~spl4_5 | spl4_23 | ~spl4_19),
% 1.64/0.58    inference(avatar_split_clause,[],[f425,f373,f428,f184])).
% 1.64/0.58  fof(f373,plain,(
% 1.64/0.58    spl4_19 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.64/0.58  fof(f425,plain,(
% 1.64/0.58    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_19),
% 1.64/0.58    inference(superposition,[],[f104,f375])).
% 1.64/0.58  fof(f375,plain,(
% 1.64/0.58    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_19),
% 1.64/0.58    inference(avatar_component_clause,[],[f373])).
% 1.64/0.58  fof(f104,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f48])).
% 1.64/0.58  fof(f48,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.58    inference(ennf_transformation,[],[f16])).
% 1.64/0.58  fof(f16,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.64/0.58  fof(f422,plain,(
% 1.64/0.58    ~spl4_21 | spl4_22 | ~spl4_16),
% 1.64/0.58    inference(avatar_split_clause,[],[f411,f360,f418,f414])).
% 1.64/0.58  fof(f360,plain,(
% 1.64/0.58    spl4_16 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.64/0.58  fof(f411,plain,(
% 1.64/0.58    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_16),
% 1.64/0.58    inference(superposition,[],[f104,f362])).
% 1.64/0.58  fof(f362,plain,(
% 1.64/0.58    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_16),
% 1.64/0.58    inference(avatar_component_clause,[],[f360])).
% 1.64/0.58  fof(f408,plain,(
% 1.64/0.58    ~spl4_20),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f397])).
% 1.64/0.58  fof(f397,plain,(
% 1.64/0.58    $false | ~spl4_20),
% 1.64/0.58    inference(subsumption_resolution,[],[f71,f379])).
% 1.64/0.58  fof(f379,plain,(
% 1.64/0.58    k1_xboole_0 = sK1 | ~spl4_20),
% 1.64/0.58    inference(avatar_component_clause,[],[f377])).
% 1.64/0.58  fof(f377,plain,(
% 1.64/0.58    spl4_20 <=> k1_xboole_0 = sK1),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.64/0.58  fof(f71,plain,(
% 1.64/0.58    k1_xboole_0 != sK1),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f396,plain,(
% 1.64/0.58    spl4_18),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f395])).
% 1.64/0.58  fof(f395,plain,(
% 1.64/0.58    $false | spl4_18),
% 1.64/0.58    inference(subsumption_resolution,[],[f74,f371])).
% 1.64/0.58  fof(f371,plain,(
% 1.64/0.58    ~v1_funct_2(sK2,sK0,sK1) | spl4_18),
% 1.64/0.58    inference(avatar_component_clause,[],[f369])).
% 1.64/0.58  fof(f74,plain,(
% 1.64/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f394,plain,(
% 1.64/0.58    ~spl4_17),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f386])).
% 1.64/0.58  fof(f386,plain,(
% 1.64/0.58    $false | ~spl4_17),
% 1.64/0.58    inference(subsumption_resolution,[],[f70,f366])).
% 1.64/0.58  fof(f366,plain,(
% 1.64/0.58    k1_xboole_0 = sK0 | ~spl4_17),
% 1.64/0.58    inference(avatar_component_clause,[],[f364])).
% 1.64/0.58  fof(f70,plain,(
% 1.64/0.58    k1_xboole_0 != sK0),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f385,plain,(
% 1.64/0.58    spl4_15),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f384])).
% 1.64/0.58  fof(f384,plain,(
% 1.64/0.58    $false | spl4_15),
% 1.64/0.58    inference(subsumption_resolution,[],[f65,f358])).
% 1.64/0.58  fof(f358,plain,(
% 1.64/0.58    ~v1_funct_2(sK3,sK1,sK0) | spl4_15),
% 1.64/0.58    inference(avatar_component_clause,[],[f356])).
% 1.64/0.58  fof(f65,plain,(
% 1.64/0.58    v1_funct_2(sK3,sK1,sK0)),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f380,plain,(
% 1.64/0.58    ~spl4_18 | spl4_19 | spl4_20),
% 1.64/0.58    inference(avatar_split_clause,[],[f354,f377,f373,f369])).
% 1.64/0.58  fof(f354,plain,(
% 1.64/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.64/0.58    inference(resolution,[],[f111,f75])).
% 1.64/0.58  fof(f111,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f51])).
% 1.64/0.58  fof(f51,plain,(
% 1.64/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.58    inference(flattening,[],[f50])).
% 1.64/0.58  fof(f50,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.58    inference(ennf_transformation,[],[f19])).
% 1.64/0.58  fof(f19,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.64/0.58  fof(f367,plain,(
% 1.64/0.58    ~spl4_15 | spl4_16 | spl4_17),
% 1.64/0.58    inference(avatar_split_clause,[],[f352,f364,f360,f356])).
% 1.64/0.58  fof(f352,plain,(
% 1.64/0.58    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.64/0.58    inference(resolution,[],[f111,f66])).
% 1.64/0.58  fof(f333,plain,(
% 1.64/0.58    spl4_13),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f332])).
% 1.64/0.58  fof(f332,plain,(
% 1.64/0.58    $false | spl4_13),
% 1.64/0.58    inference(subsumption_resolution,[],[f73,f327])).
% 1.64/0.58  fof(f327,plain,(
% 1.64/0.58    ~v1_funct_1(sK2) | spl4_13),
% 1.64/0.58    inference(avatar_component_clause,[],[f325])).
% 1.64/0.58  fof(f331,plain,(
% 1.64/0.58    ~spl4_13 | ~spl4_3 | spl4_14 | ~spl4_6),
% 1.64/0.58    inference(avatar_split_clause,[],[f319,f188,f329,f155,f325])).
% 1.64/0.58  fof(f319,plain,(
% 1.64/0.58    ( ! [X8] : (sK1 != k1_relat_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,X8)) | ~v1_relat_1(X8) | v2_funct_1(X8)) ) | ~spl4_6),
% 1.64/0.58    inference(superposition,[],[f102,f190])).
% 1.64/0.58  fof(f102,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f47])).
% 1.64/0.58  fof(f47,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.58    inference(flattening,[],[f46])).
% 1.64/0.58  fof(f46,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.64/0.58    inference(ennf_transformation,[],[f10])).
% 1.64/0.58  fof(f10,axiom,(
% 1.64/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 1.64/0.58  fof(f194,plain,(
% 1.64/0.58    spl4_5),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f193])).
% 1.64/0.58  fof(f193,plain,(
% 1.64/0.58    $false | spl4_5),
% 1.64/0.58    inference(subsumption_resolution,[],[f75,f186])).
% 1.64/0.58  fof(f186,plain,(
% 1.64/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 1.64/0.58    inference(avatar_component_clause,[],[f184])).
% 1.64/0.58  fof(f192,plain,(
% 1.64/0.58    ~spl4_5 | spl4_6),
% 1.64/0.58    inference(avatar_split_clause,[],[f182,f188,f184])).
% 1.64/0.58  fof(f182,plain,(
% 1.64/0.58    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.64/0.58    inference(superposition,[],[f67,f105])).
% 1.64/0.58  fof(f67,plain,(
% 1.64/0.58    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.64/0.58    inference(cnf_transformation,[],[f30])).
% 1.64/0.58  fof(f170,plain,(
% 1.64/0.58    spl4_4),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f167])).
% 1.64/0.58  fof(f167,plain,(
% 1.64/0.58    $false | spl4_4),
% 1.64/0.58    inference(unit_resulting_resolution,[],[f103,f161])).
% 1.64/0.58  fof(f161,plain,(
% 1.64/0.58    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 1.64/0.58    inference(avatar_component_clause,[],[f159])).
% 1.64/0.58  fof(f159,plain,(
% 1.64/0.58    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.64/0.58  fof(f103,plain,(
% 1.64/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f2])).
% 1.64/0.58  fof(f2,axiom,(
% 1.64/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.64/0.58  fof(f166,plain,(
% 1.64/0.58    spl4_2),
% 1.64/0.58    inference(avatar_contradiction_clause,[],[f163])).
% 1.64/0.58  fof(f163,plain,(
% 1.64/0.58    $false | spl4_2),
% 1.64/0.58    inference(unit_resulting_resolution,[],[f103,f152])).
% 1.64/0.58  fof(f152,plain,(
% 1.64/0.58    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 1.64/0.58    inference(avatar_component_clause,[],[f150])).
% 1.64/0.58  fof(f150,plain,(
% 1.64/0.58    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.64/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.64/0.58  fof(f162,plain,(
% 1.64/0.58    spl4_3 | ~spl4_4),
% 1.64/0.58    inference(avatar_split_clause,[],[f143,f159,f155])).
% 1.64/0.58  fof(f143,plain,(
% 1.64/0.58    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.64/0.58    inference(resolution,[],[f88,f75])).
% 1.64/0.58  fof(f88,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f33])).
% 1.64/0.58  fof(f33,plain,(
% 1.64/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.64/0.58    inference(ennf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.64/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.64/0.58  fof(f153,plain,(
% 1.64/0.58    spl4_1 | ~spl4_2),
% 1.64/0.58    inference(avatar_split_clause,[],[f142,f150,f146])).
% 1.64/0.58  fof(f142,plain,(
% 1.64/0.58    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.64/0.58    inference(resolution,[],[f88,f66])).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (3527)------------------------------
% 1.64/0.58  % (3527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (3527)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (3527)Memory used [KB]: 7419
% 1.64/0.58  % (3527)Time elapsed: 0.125 s
% 1.64/0.58  % (3527)------------------------------
% 1.64/0.58  % (3527)------------------------------
% 1.64/0.59  % (3505)Success in time 0.219 s
%------------------------------------------------------------------------------
