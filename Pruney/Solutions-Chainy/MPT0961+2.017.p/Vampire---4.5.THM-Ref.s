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
% DateTime   : Thu Dec  3 13:00:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 203 expanded)
%              Number of leaves         :   26 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  335 ( 618 expanded)
%              Number of equality atoms :   85 ( 197 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f77,f82,f96,f100,f110,f122,f128,f142,f145,f160,f165,f183,f195,f200,f219,f245])).

fof(f245,plain,
    ( spl1_19
    | ~ spl1_20
    | ~ spl1_23 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl1_19
    | ~ spl1_20
    | ~ spl1_23 ),
    inference(subsumption_resolution,[],[f243,f199])).

fof(f199,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl1_20
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f243,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl1_19
    | ~ spl1_23 ),
    inference(forward_demodulation,[],[f242,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f242,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl1_19
    | ~ spl1_23 ),
    inference(subsumption_resolution,[],[f238,f194])).

fof(f194,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl1_19
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f238,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl1_23 ),
    inference(trivial_inequality_removal,[],[f237])).

fof(f237,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl1_23 ),
    inference(superposition,[],[f58,f215])).

fof(f215,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl1_23
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f58,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f219,plain,
    ( spl1_23
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f218,f157,f130,f213])).

fof(f130,plain,
    ( spl1_10
  <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f157,plain,
    ( spl1_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f218,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f217,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f217,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl1_10
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f132,f159])).

fof(f159,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f157])).

fof(f132,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f200,plain,
    ( spl1_20
    | ~ spl1_11
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f186,f157,f139,f197])).

fof(f139,plain,
    ( spl1_11
  <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f186,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_11
    | ~ spl1_13 ),
    inference(backward_demodulation,[],[f141,f159])).

fof(f141,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f195,plain,
    ( ~ spl1_19
    | ~ spl1_13
    | spl1_14 ),
    inference(avatar_split_clause,[],[f190,f162,f157,f192])).

fof(f162,plain,
    ( spl1_14
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f190,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_13
    | spl1_14 ),
    inference(forward_demodulation,[],[f184,f44])).

fof(f184,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl1_13
    | spl1_14 ),
    inference(backward_demodulation,[],[f164,f159])).

fof(f164,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f183,plain,
    ( spl1_10
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f147,f125,f118,f130])).

fof(f118,plain,
    ( spl1_8
  <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f125,plain,
    ( spl1_9
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f147,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0)
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f120,f127])).

fof(f127,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f120,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f165,plain,
    ( ~ spl1_14
    | spl1_2
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f136,f125,f69,f162])).

fof(f69,plain,
    ( spl1_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f136,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_2
    | ~ spl1_9 ),
    inference(backward_demodulation,[],[f71,f127])).

fof(f71,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f160,plain,
    ( spl1_13
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f155,f125,f102,f157])).

fof(f102,plain,
    ( spl1_6
  <=> sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f155,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f154,f62])).

fof(f154,plain,
    ( sK0 = k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)
    | ~ spl1_6
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f104,f127])).

fof(f104,plain,
    ( sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f145,plain,
    ( spl1_7
    | ~ spl1_9 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl1_7
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f143,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f143,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl1_7
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f134,f62])).

fof(f134,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0),sK0)
    | spl1_7
    | ~ spl1_9 ),
    inference(backward_demodulation,[],[f108,f127])).

fof(f108,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | spl1_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl1_7
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f142,plain,
    ( spl1_11
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f137,f125,f73,f139])).

fof(f73,plain,
    ( spl1_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f137,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f133,f62])).

fof(f133,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(backward_demodulation,[],[f74,f127])).

fof(f74,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f128,plain,
    ( spl1_9
    | ~ spl1_8
    | spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f123,f73,f69,f118,f125])).

fof(f123,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | spl1_2
    | ~ spl1_3 ),
    inference(subsumption_resolution,[],[f115,f71])).

fof(f115,plain,
    ( k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f122,plain,
    ( spl1_8
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f113,f73,f118])).

fof(f113,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f110,plain,
    ( spl1_6
    | ~ spl1_7
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f99,f93,f106,f102])).

fof(f93,plain,
    ( spl1_5
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f99,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_5 ),
    inference(resolution,[],[f95,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f95,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f100,plain,
    ( spl1_3
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f97,f93,f73])).

fof(f97,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f95,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f96,plain,
    ( spl1_5
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f83,f79,f93])).

fof(f79,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f83,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f81,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f81,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f82,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f30,f79])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f77,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f65,plain,
    ( spl1_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f32,f73,f69,f65])).

fof(f32,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:59:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.50  % (18068)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (18048)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (18060)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (18064)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (18049)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (18052)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (18066)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (18051)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (18063)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (18051)Refutation not found, incomplete strategy% (18051)------------------------------
% 0.22/0.51  % (18051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18051)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (18051)Memory used [KB]: 6140
% 0.22/0.51  % (18051)Time elapsed: 0.097 s
% 0.22/0.51  % (18051)------------------------------
% 0.22/0.51  % (18051)------------------------------
% 0.22/0.52  % (18052)Refutation not found, incomplete strategy% (18052)------------------------------
% 0.22/0.52  % (18052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18052)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18052)Memory used [KB]: 10618
% 0.22/0.52  % (18052)Time elapsed: 0.063 s
% 0.22/0.52  % (18052)------------------------------
% 0.22/0.52  % (18052)------------------------------
% 0.22/0.52  % (18059)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (18056)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (18059)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f246,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f76,f77,f82,f96,f100,f110,f122,f128,f142,f145,f160,f165,f183,f195,f200,f219,f245])).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    spl1_19 | ~spl1_20 | ~spl1_23),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f244])).
% 0.22/0.52  fof(f244,plain,(
% 0.22/0.52    $false | (spl1_19 | ~spl1_20 | ~spl1_23)),
% 0.22/0.52    inference(subsumption_resolution,[],[f243,f199])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl1_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f197])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    spl1_20 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl1_19 | ~spl1_23)),
% 0.22/0.52    inference(forward_demodulation,[],[f242,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.52    inference(flattening,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f242,plain,(
% 0.22/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl1_19 | ~spl1_23)),
% 0.22/0.52    inference(subsumption_resolution,[],[f238,f194])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl1_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f192])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    spl1_19 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.22/0.52  fof(f238,plain,(
% 0.22/0.52    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl1_23),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f237])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl1_23),
% 0.22/0.52    inference(superposition,[],[f58,f215])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl1_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f213])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    spl1_23 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.52    inference(equality_resolution,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f219,plain,(
% 0.22/0.52    spl1_23 | ~spl1_10 | ~spl1_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f218,f157,f130,f213])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    spl1_10 <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    spl1_13 <=> k1_xboole_0 = sK0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_10 | ~spl1_13)),
% 0.22/0.52    inference(forward_demodulation,[],[f217,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl1_10 | ~spl1_13)),
% 0.22/0.52    inference(forward_demodulation,[],[f132,f159])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | ~spl1_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f157])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0) | ~spl1_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f130])).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    spl1_20 | ~spl1_11 | ~spl1_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f186,f157,f139,f197])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    spl1_11 <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl1_11 | ~spl1_13)),
% 0.22/0.52    inference(backward_demodulation,[],[f141,f159])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~spl1_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f139])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    ~spl1_19 | ~spl1_13 | spl1_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f190,f162,f157,f192])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    spl1_14 <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_13 | spl1_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f184,f44])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl1_13 | spl1_14)),
% 0.22/0.52    inference(backward_demodulation,[],[f164,f159])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | spl1_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f162])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    spl1_10 | ~spl1_8 | ~spl1_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f147,f125,f118,f130])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl1_8 <=> k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    spl1_9 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k1_xboole_0,sK0) | (~spl1_8 | ~spl1_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f120,f127])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f125])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | ~spl1_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f118])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    ~spl1_14 | spl1_2 | ~spl1_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f136,f125,f69,f162])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl1_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl1_2 | ~spl1_9)),
% 0.22/0.52    inference(backward_demodulation,[],[f71,f127])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl1_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f69])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    spl1_13 | ~spl1_6 | ~spl1_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f155,f125,f102,f157])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    spl1_6 <=> sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | (~spl1_6 | ~spl1_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f154,f62])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    sK0 = k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0) | (~spl1_6 | ~spl1_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f104,f127])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f102])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    spl1_7 | ~spl1_9),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f144])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    $false | (spl1_7 | ~spl1_9)),
% 0.22/0.52    inference(subsumption_resolution,[],[f143,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,sK0) | (spl1_7 | ~spl1_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f134,f62])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0),sK0) | (spl1_7 | ~spl1_9)),
% 0.22/0.52    inference(backward_demodulation,[],[f108,f127])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) | spl1_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f106])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    spl1_7 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    spl1_11 | ~spl1_3 | ~spl1_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f137,f125,f73,f139])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl1_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | (~spl1_3 | ~spl1_9)),
% 0.22/0.52    inference(forward_demodulation,[],[f133,f62])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) | (~spl1_3 | ~spl1_9)),
% 0.22/0.52    inference(backward_demodulation,[],[f74,f127])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl1_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    spl1_9 | ~spl1_8 | spl1_2 | ~spl1_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f123,f73,f69,f118,f125])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | (spl1_2 | ~spl1_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f115,f71])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_3),
% 0.22/0.52    inference(resolution,[],[f74,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    spl1_8 | ~spl1_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f113,f73,f118])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | ~spl1_3),
% 0.22/0.52    inference(resolution,[],[f74,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    spl1_6 | ~spl1_7 | ~spl1_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f99,f93,f106,f102])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    spl1_5 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) | sK0 = k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_5),
% 0.22/0.52    inference(resolution,[],[f95,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f93])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    spl1_3 | ~spl1_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f97,f93,f73])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl1_5),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f95,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    spl1_5 | ~spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f83,f79,f93])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl1_4 <=> v1_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_4),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f81,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    v1_relat_1(sK0) | ~spl1_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f79])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f30,f79])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f11])).
% 0.22/0.52  fof(f11,conjecture,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl1_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f31,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl1_1 <=> v1_funct_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    v1_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f32,f73,f69,f65])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (18059)------------------------------
% 0.22/0.52  % (18059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18059)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (18059)Memory used [KB]: 6268
% 0.22/0.52  % (18059)Time elapsed: 0.105 s
% 0.22/0.52  % (18059)------------------------------
% 0.22/0.52  % (18059)------------------------------
% 0.22/0.52  % (18057)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (18046)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (18043)Success in time 0.155 s
%------------------------------------------------------------------------------
