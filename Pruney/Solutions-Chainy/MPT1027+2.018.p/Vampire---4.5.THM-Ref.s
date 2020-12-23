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
% DateTime   : Thu Dec  3 13:06:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 207 expanded)
%              Number of leaves         :   28 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  362 ( 664 expanded)
%              Number of equality atoms :   88 ( 161 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f69,f70,f75,f86,f109,f119,f146,f154,f167,f173,f182,f187,f207,f227,f232,f254,f281])).

fof(f281,plain,
    ( ~ spl6_17
    | ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl6_17
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f259,f50])).

fof(f50,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f259,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_17
    | ~ spl6_27 ),
    inference(backward_demodulation,[],[f181,f253])).

fof(f253,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl6_27
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f181,plain,
    ( sP0(sK3,k1_xboole_0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl6_17
  <=> sP0(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f254,plain,
    ( spl6_27
    | spl6_23
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f247,f229,f224,f251])).

fof(f224,plain,
    ( spl6_23
  <=> v1_funct_2(k1_xboole_0,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f229,plain,
    ( spl6_24
  <=> sP2(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f247,plain,
    ( k1_xboole_0 = sK3
    | spl6_23
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f226,f231,f48])).

fof(f48,plain,(
    ! [X2] :
      ( ~ sP2(k1_xboole_0,k1_xboole_0,X2)
      | k1_xboole_0 = X2
      | v1_funct_2(k1_xboole_0,X2,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k1_xboole_0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X2,X1)
      | k1_xboole_0 != X0
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f231,plain,
    ( sP2(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f229])).

fof(f226,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK3,k1_xboole_0)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f224])).

fof(f232,plain,
    ( spl6_24
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f214,f203,f184,f229])).

fof(f184,plain,
    ( spl6_18
  <=> sP2(sK5,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f203,plain,
    ( spl6_21
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f214,plain,
    ( sP2(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(backward_demodulation,[],[f186,f205])).

fof(f205,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f203])).

fof(f186,plain,
    ( sP2(sK5,k1_xboole_0,sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f227,plain,
    ( ~ spl6_23
    | spl6_16
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f213,f203,f164,f224])).

fof(f164,plain,
    ( spl6_16
  <=> v1_funct_2(sK5,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f213,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK3,k1_xboole_0)
    | spl6_16
    | ~ spl6_21 ),
    inference(backward_demodulation,[],[f166,f205])).

fof(f166,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f207,plain,
    ( spl6_21
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f198,f83,f72,f203])).

fof(f72,plain,
    ( spl6_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f83,plain,
    ( spl6_7
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f198,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_5
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f74,f85,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f85,plain,
    ( v1_xboole_0(sK5)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f74,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f187,plain,
    ( spl6_18
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f161,f150,f115,f184])).

fof(f115,plain,
    ( spl6_11
  <=> sP2(sK5,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f150,plain,
    ( spl6_15
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f161,plain,
    ( sP2(sK5,k1_xboole_0,sK3)
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f117,f152])).

fof(f152,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f117,plain,
    ( sP2(sK5,sK4,sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f182,plain,
    ( spl6_17
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f162,f150,f140,f179])).

fof(f140,plain,
    ( spl6_14
  <=> sP0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f162,plain,
    ( sP0(sK3,k1_xboole_0)
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f142,f152])).

fof(f142,plain,
    ( sP0(sK3,sK4)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f173,plain,
    ( ~ spl6_5
    | spl6_6
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | ~ spl6_5
    | spl6_6
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f171,f74])).

fof(f171,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_6
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f158,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f158,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0))
    | spl6_6
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f81,f152])).

fof(f81,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK3,sK4))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_6
  <=> v1_xboole_0(k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f167,plain,
    ( ~ spl6_16
    | spl6_2
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f155,f150,f56,f164])).

fof(f56,plain,
    ( spl6_2
  <=> v1_funct_2(sK5,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f155,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | spl6_2
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f58,f152])).

fof(f58,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f154,plain,
    ( spl6_15
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f148,f140,f150])).

fof(f148,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_14 ),
    inference(resolution,[],[f142,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f146,plain,
    ( spl6_14
    | spl6_2
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f145,f105,f65,f56,f140])).

fof(f65,plain,
    ( spl6_4
  <=> sK3 = k1_relset_1(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f105,plain,
    ( spl6_10
  <=> sP1(sK3,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f145,plain,
    ( sP0(sK3,sK4)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f144,f107])).

fof(f107,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f144,plain,
    ( sP0(sK3,sK4)
    | ~ sP1(sK3,sK5,sK4)
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f138,f58])).

fof(f138,plain,
    ( v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( sK3 != sK3
    | v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK5,sK4)
    | ~ spl6_4 ),
    inference(superposition,[],[f40,f67])).

fof(f67,plain,
    ( sK3 = k1_relset_1(sK3,sK4,sK5)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f119,plain,
    ( spl6_11
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f111,f60,f115])).

fof(f60,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f111,plain,
    ( sP2(sK5,sK4,sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f44,f61])).

fof(f61,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f13,f16,f15,f14])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f109,plain,
    ( spl6_10
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f101,f60,f105])).

fof(f101,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ spl6_3 ),
    inference(resolution,[],[f43,f61])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,
    ( ~ spl6_6
    | spl6_7
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f77,f60,f83,f79])).

fof(f77,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k2_zfmisc_1(sK3,sK4))
    | ~ spl6_3 ),
    inference(resolution,[],[f32,f61])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f75,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f70,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f52,plain,
    ( spl6_1
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f27,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_2(sK5,sK3,sK4)
      | ~ v1_funct_1(sK5) )
    & sK3 = k1_relset_1(sK3,sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f9,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & k1_relset_1(X0,X1,X2) = X0
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        | ~ v1_funct_2(sK5,sK3,sK4)
        | ~ v1_funct_1(sK5) )
      & sK3 = k1_relset_1(sK3,sK4,sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f69,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    sK3 = k1_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f30,f60,f56,f52])).

fof(f30,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (1021)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.42  % (1021)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f282,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f63,f68,f69,f70,f75,f86,f109,f119,f146,f154,f167,f173,f182,f187,f207,f227,f232,f254,f281])).
% 0.20/0.42  fof(f281,plain,(
% 0.20/0.42    ~spl6_17 | ~spl6_27),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f280])).
% 0.20/0.43  fof(f280,plain,(
% 0.20/0.43    $false | (~spl6_17 | ~spl6_27)),
% 0.20/0.43    inference(subsumption_resolution,[],[f259,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.20/0.43    inference(equality_resolution,[],[f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.20/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.43  fof(f259,plain,(
% 0.20/0.43    sP0(k1_xboole_0,k1_xboole_0) | (~spl6_17 | ~spl6_27)),
% 0.20/0.43    inference(backward_demodulation,[],[f181,f253])).
% 0.20/0.43  fof(f253,plain,(
% 0.20/0.43    k1_xboole_0 = sK3 | ~spl6_27),
% 0.20/0.43    inference(avatar_component_clause,[],[f251])).
% 0.20/0.43  fof(f251,plain,(
% 0.20/0.43    spl6_27 <=> k1_xboole_0 = sK3),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.43  fof(f181,plain,(
% 0.20/0.43    sP0(sK3,k1_xboole_0) | ~spl6_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f179])).
% 0.20/0.43  fof(f179,plain,(
% 0.20/0.43    spl6_17 <=> sP0(sK3,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.43  fof(f254,plain,(
% 0.20/0.43    spl6_27 | spl6_23 | ~spl6_24),
% 0.20/0.43    inference(avatar_split_clause,[],[f247,f229,f224,f251])).
% 0.20/0.43  fof(f224,plain,(
% 0.20/0.43    spl6_23 <=> v1_funct_2(k1_xboole_0,sK3,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.43  fof(f229,plain,(
% 0.20/0.43    spl6_24 <=> sP2(k1_xboole_0,k1_xboole_0,sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.43  fof(f247,plain,(
% 0.20/0.43    k1_xboole_0 = sK3 | (spl6_23 | ~spl6_24)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f226,f231,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X2] : (~sP2(k1_xboole_0,k1_xboole_0,X2) | k1_xboole_0 = X2 | v1_funct_2(k1_xboole_0,X2,k1_xboole_0)) )),
% 0.20/0.43    inference(equality_resolution,[],[f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X2,X1] : (v1_funct_2(k1_xboole_0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(k1_xboole_0,X1,X2)) )),
% 0.20/0.43    inference(equality_resolution,[],[f38])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0 | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 0.20/0.43    inference(rectify,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.20/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.43  fof(f231,plain,(
% 0.20/0.43    sP2(k1_xboole_0,k1_xboole_0,sK3) | ~spl6_24),
% 0.20/0.43    inference(avatar_component_clause,[],[f229])).
% 0.20/0.43  fof(f226,plain,(
% 0.20/0.43    ~v1_funct_2(k1_xboole_0,sK3,k1_xboole_0) | spl6_23),
% 0.20/0.43    inference(avatar_component_clause,[],[f224])).
% 0.20/0.43  fof(f232,plain,(
% 0.20/0.43    spl6_24 | ~spl6_18 | ~spl6_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f214,f203,f184,f229])).
% 0.20/0.43  fof(f184,plain,(
% 0.20/0.43    spl6_18 <=> sP2(sK5,k1_xboole_0,sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.43  fof(f203,plain,(
% 0.20/0.43    spl6_21 <=> k1_xboole_0 = sK5),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.43  fof(f214,plain,(
% 0.20/0.43    sP2(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_18 | ~spl6_21)),
% 0.20/0.43    inference(backward_demodulation,[],[f186,f205])).
% 0.20/0.43  fof(f205,plain,(
% 0.20/0.43    k1_xboole_0 = sK5 | ~spl6_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f203])).
% 0.20/0.43  fof(f186,plain,(
% 0.20/0.43    sP2(sK5,k1_xboole_0,sK3) | ~spl6_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f184])).
% 0.20/0.43  fof(f227,plain,(
% 0.20/0.43    ~spl6_23 | spl6_16 | ~spl6_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f213,f203,f164,f224])).
% 0.20/0.43  fof(f164,plain,(
% 0.20/0.43    spl6_16 <=> v1_funct_2(sK5,sK3,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.43  fof(f213,plain,(
% 0.20/0.43    ~v1_funct_2(k1_xboole_0,sK3,k1_xboole_0) | (spl6_16 | ~spl6_21)),
% 0.20/0.43    inference(backward_demodulation,[],[f166,f205])).
% 0.20/0.43  fof(f166,plain,(
% 0.20/0.43    ~v1_funct_2(sK5,sK3,k1_xboole_0) | spl6_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f164])).
% 0.20/0.43  fof(f207,plain,(
% 0.20/0.43    spl6_21 | ~spl6_5 | ~spl6_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f198,f83,f72,f203])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl6_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    spl6_7 <=> v1_xboole_0(sK5)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.43  fof(f198,plain,(
% 0.20/0.43    k1_xboole_0 = sK5 | (~spl6_5 | ~spl6_7)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f74,f85,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    v1_xboole_0(sK5) | ~spl6_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f83])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0) | ~spl6_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f72])).
% 0.20/0.43  fof(f187,plain,(
% 0.20/0.43    spl6_18 | ~spl6_11 | ~spl6_15),
% 0.20/0.43    inference(avatar_split_clause,[],[f161,f150,f115,f184])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    spl6_11 <=> sP2(sK5,sK4,sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.43  fof(f150,plain,(
% 0.20/0.43    spl6_15 <=> k1_xboole_0 = sK4),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.43  fof(f161,plain,(
% 0.20/0.43    sP2(sK5,k1_xboole_0,sK3) | (~spl6_11 | ~spl6_15)),
% 0.20/0.43    inference(backward_demodulation,[],[f117,f152])).
% 0.20/0.43  fof(f152,plain,(
% 0.20/0.43    k1_xboole_0 = sK4 | ~spl6_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f150])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    sP2(sK5,sK4,sK3) | ~spl6_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f115])).
% 0.20/0.43  fof(f182,plain,(
% 0.20/0.43    spl6_17 | ~spl6_14 | ~spl6_15),
% 0.20/0.43    inference(avatar_split_clause,[],[f162,f150,f140,f179])).
% 0.20/0.43  fof(f140,plain,(
% 0.20/0.43    spl6_14 <=> sP0(sK3,sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.43  fof(f162,plain,(
% 0.20/0.43    sP0(sK3,k1_xboole_0) | (~spl6_14 | ~spl6_15)),
% 0.20/0.43    inference(backward_demodulation,[],[f142,f152])).
% 0.20/0.43  fof(f142,plain,(
% 0.20/0.43    sP0(sK3,sK4) | ~spl6_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f140])).
% 0.20/0.43  fof(f173,plain,(
% 0.20/0.43    ~spl6_5 | spl6_6 | ~spl6_15),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f172])).
% 0.20/0.43  fof(f172,plain,(
% 0.20/0.43    $false | (~spl6_5 | spl6_6 | ~spl6_15)),
% 0.20/0.43    inference(subsumption_resolution,[],[f171,f74])).
% 0.20/0.43  fof(f171,plain,(
% 0.20/0.43    ~v1_xboole_0(k1_xboole_0) | (spl6_6 | ~spl6_15)),
% 0.20/0.43    inference(forward_demodulation,[],[f158,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(equality_resolution,[],[f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.43    inference(flattening,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.43  fof(f158,plain,(
% 0.20/0.43    ~v1_xboole_0(k2_zfmisc_1(sK3,k1_xboole_0)) | (spl6_6 | ~spl6_15)),
% 0.20/0.43    inference(backward_demodulation,[],[f81,f152])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ~v1_xboole_0(k2_zfmisc_1(sK3,sK4)) | spl6_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f79])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    spl6_6 <=> v1_xboole_0(k2_zfmisc_1(sK3,sK4))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.43  fof(f167,plain,(
% 0.20/0.43    ~spl6_16 | spl6_2 | ~spl6_15),
% 0.20/0.43    inference(avatar_split_clause,[],[f155,f150,f56,f164])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl6_2 <=> v1_funct_2(sK5,sK3,sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.43  fof(f155,plain,(
% 0.20/0.43    ~v1_funct_2(sK5,sK3,k1_xboole_0) | (spl6_2 | ~spl6_15)),
% 0.20/0.43    inference(backward_demodulation,[],[f58,f152])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ~v1_funct_2(sK5,sK3,sK4) | spl6_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f56])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    spl6_15 | ~spl6_14),
% 0.20/0.43    inference(avatar_split_clause,[],[f148,f140,f150])).
% 0.20/0.43  fof(f148,plain,(
% 0.20/0.43    k1_xboole_0 = sK4 | ~spl6_14),
% 0.20/0.43    inference(resolution,[],[f142,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f26])).
% 0.20/0.43  fof(f146,plain,(
% 0.20/0.43    spl6_14 | spl6_2 | ~spl6_4 | ~spl6_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f145,f105,f65,f56,f140])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl6_4 <=> sK3 = k1_relset_1(sK3,sK4,sK5)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    spl6_10 <=> sP1(sK3,sK5,sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.43  fof(f145,plain,(
% 0.20/0.43    sP0(sK3,sK4) | (spl6_2 | ~spl6_4 | ~spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f144,f107])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    sP1(sK3,sK5,sK4) | ~spl6_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f105])).
% 0.20/0.43  fof(f144,plain,(
% 0.20/0.43    sP0(sK3,sK4) | ~sP1(sK3,sK5,sK4) | (spl6_2 | ~spl6_4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f138,f58])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | ~sP1(sK3,sK5,sK4) | ~spl6_4),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f135])).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    sK3 != sK3 | v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | ~sP1(sK3,sK5,sK4) | ~spl6_4),
% 0.20/0.43    inference(superposition,[],[f40,f67])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    sK3 = k1_relset_1(sK3,sK4,sK5) | ~spl6_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f65])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.20/0.43    inference(rectify,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.20/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    spl6_11 | ~spl6_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f111,f60,f115])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl6_3 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    sP2(sK5,sK4,sK3) | ~spl6_3),
% 0.20/0.43    inference(resolution,[],[f44,f61])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~spl6_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f60])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(definition_folding,[],[f13,f16,f15,f14])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(flattening,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    spl6_10 | ~spl6_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f101,f60,f105])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    sP1(sK3,sK5,sK4) | ~spl6_3),
% 0.20/0.43    inference(resolution,[],[f43,f61])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    ~spl6_6 | spl6_7 | ~spl6_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f77,f60,f83,f79])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    v1_xboole_0(sK5) | ~v1_xboole_0(k2_zfmisc_1(sK3,sK4)) | ~spl6_3),
% 0.20/0.43    inference(resolution,[],[f32,f61])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    spl6_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f72])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    spl6_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl6_1 <=> v1_funct_1(sK5)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    v1_funct_1(sK5)),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)) & sK3 = k1_relset_1(sK3,sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f9,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)) & sK3 = k1_relset_1(sK3,sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.43    inference(flattening,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.43    inference(negated_conjecture,[],[f6])).
% 0.20/0.43  fof(f6,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl6_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f60])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    spl6_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f65])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    sK3 = k1_relset_1(sK3,sK4,sK5)),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f30,f60,f56,f52])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (1021)------------------------------
% 0.20/0.43  % (1021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (1021)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (1021)Memory used [KB]: 10746
% 0.20/0.43  % (1021)Time elapsed: 0.009 s
% 0.20/0.43  % (1021)------------------------------
% 0.20/0.43  % (1021)------------------------------
% 0.20/0.43  % (1004)Success in time 0.073 s
%------------------------------------------------------------------------------
