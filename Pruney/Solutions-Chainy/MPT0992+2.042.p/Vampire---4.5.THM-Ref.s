%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 363 expanded)
%              Number of leaves         :   46 ( 149 expanded)
%              Depth                    :    9
%              Number of atoms          :  609 (1323 expanded)
%              Number of equality atoms :   74 ( 173 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f765,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f105,f109,f113,f117,f121,f198,f274,f336,f344,f348,f351,f369,f387,f393,f409,f427,f440,f461,f465,f477,f484,f610,f630,f631,f674,f684,f702,f726,f763,f764])).

fof(f764,plain,
    ( k1_xboole_0 != sK2
    | r1_tarski(sK2,k1_relat_1(sK3))
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f763,plain,
    ( spl4_81
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f752,f628,f761])).

fof(f761,plain,
    ( spl4_81
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f628,plain,
    ( spl4_64
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f752,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_64 ),
    inference(resolution,[],[f629,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f629,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f628])).

fof(f726,plain,
    ( spl4_40
    | ~ spl4_41
    | ~ spl4_49
    | spl4_69 ),
    inference(avatar_split_clause,[],[f676,f672,f482,f438,f435])).

fof(f435,plain,
    ( spl4_40
  <=> ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f438,plain,
    ( spl4_41
  <=> r1_tarski(sK2,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f482,plain,
    ( spl4_49
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(X0,k1_relat_1(sK3))
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f672,plain,
    ( spl4_69
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f676,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k1_relat_1(sK3))
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | ~ spl4_49
    | spl4_69 ),
    inference(resolution,[],[f673,f483])).

fof(f483,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(X0,k1_relat_1(sK3))
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f482])).

fof(f673,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_69 ),
    inference(avatar_component_clause,[],[f672])).

fof(f702,plain,
    ( ~ spl4_7
    | ~ spl4_35
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f701])).

fof(f701,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_35
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f112,f696])).

fof(f696,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_35
    | ~ spl4_40 ),
    inference(resolution,[],[f436,f368])).

fof(f368,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl4_35
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f436,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f435])).

fof(f112,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f684,plain,
    ( spl4_40
    | ~ spl4_6
    | ~ spl4_49
    | ~ spl4_61
    | spl4_69 ),
    inference(avatar_split_clause,[],[f682,f672,f608,f482,f107,f435])).

fof(f107,plain,
    ( spl4_6
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f608,plain,
    ( spl4_61
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f682,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,sK0)
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | ~ spl4_49
    | ~ spl4_61
    | spl4_69 ),
    inference(forward_demodulation,[],[f676,f609])).

fof(f609,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f608])).

fof(f674,plain,
    ( ~ spl4_7
    | ~ spl4_69
    | spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f666,f119,f96,f672,f111])).

fof(f96,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f119,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f666,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_9 ),
    inference(superposition,[],[f97,f313])).

fof(f313,plain,
    ( ! [X2,X0,X1] :
        ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_9 ),
    inference(resolution,[],[f79,f120])).

fof(f120,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f97,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f631,plain,
    ( sK0 != k1_relat_1(sK3)
    | r1_tarski(sK2,k1_relat_1(sK3))
    | ~ r1_tarski(sK2,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f630,plain,
    ( spl4_64
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f614,f107,f103,f628])).

fof(f103,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f614,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f108,f104])).

fof(f104,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f108,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f610,plain,
    ( ~ spl4_7
    | spl4_4
    | spl4_61
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f602,f115,f608,f100,f111])).

fof(f100,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f115,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f602,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_8 ),
    inference(resolution,[],[f400,f116])).

fof(f116,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f400,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X5,X3,X4)
      | k1_relat_1(X5) = X3
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f73,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f484,plain,
    ( ~ spl4_18
    | spl4_49
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f479,f475,f482,f190])).

fof(f190,plain,
    ( spl4_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f475,plain,
    ( spl4_48
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f479,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ r1_tarski(X0,k1_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl4_48 ),
    inference(superposition,[],[f476,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

% (5440)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f476,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X2)))
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f475])).

fof(f477,plain,
    ( ~ spl4_18
    | spl4_48
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f472,f407,f475,f190])).

fof(f407,plain,
    ( spl4_38
  <=> ! [X1,X0] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f472,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X2)))
        | ~ v1_relat_1(sK3) )
    | ~ spl4_38 ),
    inference(resolution,[],[f410,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f410,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X0))
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1))) )
    | ~ spl4_38 ),
    inference(resolution,[],[f408,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f72,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f408,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1)
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1))) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f407])).

fof(f465,plain,(
    spl4_46 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | spl4_46 ),
    inference(resolution,[],[f460,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f460,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK3)))
    | spl4_46 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl4_46
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f461,plain,
    ( ~ spl4_46
    | spl4_44 ),
    inference(avatar_split_clause,[],[f457,f448,f459])).

fof(f448,plain,
    ( spl4_44
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f457,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK3)))
    | spl4_44 ),
    inference(resolution,[],[f449,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f449,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f448])).

fof(f440,plain,
    ( spl4_40
    | ~ spl4_41
    | spl4_34
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f432,f425,f346,f438,f435])).

fof(f346,plain,
    ( spl4_34
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f425,plain,
    ( spl4_39
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,k1_relat_1(sK3))
        | v1_funct_2(k7_relat_1(sK3,X0),X0,X2)
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f432,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k1_relat_1(sK3))
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl4_34
    | ~ spl4_39 ),
    inference(resolution,[],[f426,f347])).

fof(f347,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f346])).

fof(f426,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k7_relat_1(sK3,X0),X0,X2)
        | ~ r1_tarski(X0,k1_relat_1(sK3))
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f425])).

fof(f427,plain,
    ( ~ spl4_18
    | spl4_39
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f422,f391,f425,f190])).

fof(f391,plain,
    ( spl4_37
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK3))
        | v1_funct_2(k7_relat_1(sK3,X0),X0,X1)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f422,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k1_relat_1(sK3))
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_2(k7_relat_1(sK3,X0),X0,X2)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_37 ),
    inference(resolution,[],[f394,f57])).

fof(f394,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X0))
        | ~ r1_tarski(X0,k1_relat_1(sK3))
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | v1_funct_2(k7_relat_1(sK3,X0),X0,X1) )
    | ~ spl4_37 ),
    inference(resolution,[],[f392,f155])).

fof(f392,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1)
        | v1_funct_2(k7_relat_1(sK3,X0),X0,X1)
        | ~ r1_tarski(X0,k1_relat_1(sK3)) )
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f391])).

fof(f409,plain,
    ( ~ spl4_18
    | spl4_38
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f404,f342,f407,f190])).

fof(f342,plain,
    ( spl4_33
  <=> ! [X12] : v1_funct_1(k7_relat_1(sK3,X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f404,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_33 ),
    inference(resolution,[],[f353,f57])).

fof(f353,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X4))
        | m1_subset_1(k7_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X4)),X5)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),X5) )
    | ~ spl4_33 ),
    inference(resolution,[],[f343,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f343,plain,
    ( ! [X12] : v1_funct_1(k7_relat_1(sK3,X12))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f342])).

fof(f393,plain,
    ( ~ spl4_18
    | spl4_37
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f388,f385,f391,f190])).

fof(f385,plain,
    ( spl4_36
  <=> ! [X1,X0] :
        ( v1_funct_2(k7_relat_1(sK3,X0),X0,X1)
        | ~ r1_tarski(X0,k1_relat_1(sK3))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1)
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f388,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_relat_1(sK3))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1)
        | v1_funct_2(k7_relat_1(sK3,X0),X0,X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_36 ),
    inference(resolution,[],[f386,f57])).

fof(f386,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X0))
        | ~ r1_tarski(X0,k1_relat_1(sK3))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1)
        | v1_funct_2(k7_relat_1(sK3,X0),X0,X1) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f385])).

fof(f387,plain,
    ( ~ spl4_18
    | spl4_36
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f383,f334,f385,f190])).

fof(f334,plain,
    ( spl4_31
  <=> ! [X3,X2] :
        ( v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ v1_relat_1(k7_relat_1(sK3,X2))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f383,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k7_relat_1(sK3,X0),X0,X1)
        | ~ v1_relat_1(k7_relat_1(sK3,X0))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1)
        | ~ r1_tarski(X0,k1_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl4_31 ),
    inference(superposition,[],[f335,f59])).

fof(f335,plain,
    ( ! [X2,X3] :
        ( v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ v1_relat_1(k7_relat_1(sK3,X2))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f334])).

fof(f369,plain,
    ( ~ spl4_9
    | spl4_35
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f364,f119,f367,f119])).

fof(f364,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f361])).

% (5441)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f361,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_9 ),
    inference(superposition,[],[f81,f313])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f351,plain,
    ( ~ spl4_7
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f112,f332])).

fof(f332,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl4_30
  <=> ! [X1,X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f348,plain,
    ( ~ spl4_7
    | ~ spl4_34
    | spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f326,f119,f93,f346,f111])).

fof(f93,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f326,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_2
    | ~ spl4_9 ),
    inference(superposition,[],[f94,f313])).

fof(f94,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f344,plain,
    ( spl4_30
    | spl4_33
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f327,f119,f342,f331])).

fof(f327,plain,
    ( ! [X12,X10,X11] :
        ( v1_funct_1(k7_relat_1(sK3,X12))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( ! [X12,X10,X11] :
        ( v1_funct_1(k7_relat_1(sK3,X12))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
    | ~ spl4_9 ),
    inference(superposition,[],[f269,f313])).

fof(f269,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_9 ),
    inference(resolution,[],[f80,f120])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f336,plain,
    ( spl4_30
    | spl4_31
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f329,f119,f334,f331])).

fof(f329,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_relat_1(k7_relat_1(sK3,X2)) )
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f323])).

fof(f323,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_relat_1(k7_relat_1(sK3,X2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_9 ),
    inference(superposition,[],[f272,f313])).

fof(f272,plain,
    ( ! [X6,X8,X7,X9] :
        ( v1_funct_2(k2_partfun1(X6,X7,sK3,X8),k1_relat_1(k2_partfun1(X6,X7,sK3,X8)),X9)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(X6,X7,sK3,X8)),X9)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_relat_1(k2_partfun1(X6,X7,sK3,X8)) )
    | ~ spl4_9 ),
    inference(resolution,[],[f269,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f274,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f270,f119,f90,f111])).

fof(f90,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f270,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_9 ),
    inference(resolution,[],[f269,f91])).

fof(f91,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f198,plain,
    ( ~ spl4_7
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f197])).

% (5437)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f197,plain,
    ( $false
    | ~ spl4_7
    | spl4_18 ),
    inference(subsumption_resolution,[],[f112,f196])).

fof(f196,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_18 ),
    inference(resolution,[],[f191,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f191,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f121,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f48,f119])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f117,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f49,f115])).

fof(f49,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f50,f111])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f51,f107])).

fof(f51,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f52,f103,f100])).

fof(f52,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f96,f93,f90])).

fof(f53,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (5427)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (5426)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (5436)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (5428)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (5435)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (5425)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (5433)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (5434)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (5424)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (5422)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (5423)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (5423)Refutation not found, incomplete strategy% (5423)------------------------------
% 0.21/0.51  % (5423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5423)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5423)Memory used [KB]: 10618
% 0.21/0.51  % (5423)Time elapsed: 0.091 s
% 0.21/0.51  % (5423)------------------------------
% 0.21/0.51  % (5423)------------------------------
% 0.21/0.51  % (5439)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (5438)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (5428)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f765,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f98,f105,f109,f113,f117,f121,f198,f274,f336,f344,f348,f351,f369,f387,f393,f409,f427,f440,f461,f465,f477,f484,f610,f630,f631,f674,f684,f702,f726,f763,f764])).
% 0.21/0.51  fof(f764,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | r1_tarski(sK2,k1_relat_1(sK3)) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK3))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f763,plain,(
% 0.21/0.51    spl4_81 | ~spl4_64),
% 0.21/0.51    inference(avatar_split_clause,[],[f752,f628,f761])).
% 0.21/0.51  fof(f761,plain,(
% 0.21/0.51    spl4_81 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 0.21/0.51  fof(f628,plain,(
% 0.21/0.51    spl4_64 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.21/0.51  fof(f752,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl4_64),
% 0.21/0.51    inference(resolution,[],[f629,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.51  fof(f629,plain,(
% 0.21/0.51    r1_tarski(sK2,k1_xboole_0) | ~spl4_64),
% 0.21/0.51    inference(avatar_component_clause,[],[f628])).
% 0.21/0.51  fof(f726,plain,(
% 0.21/0.51    spl4_40 | ~spl4_41 | ~spl4_49 | spl4_69),
% 0.21/0.51    inference(avatar_split_clause,[],[f676,f672,f482,f438,f435])).
% 0.21/0.51  fof(f435,plain,(
% 0.21/0.51    spl4_40 <=> ! [X0] : ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.51  fof(f438,plain,(
% 0.21/0.51    spl4_41 <=> r1_tarski(sK2,k1_relat_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.51  fof(f482,plain,(
% 0.21/0.51    spl4_49 <=> ! [X1,X0,X2] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X0,k1_relat_1(sK3)) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.51  fof(f672,plain,(
% 0.21/0.51    spl4_69 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.21/0.51  fof(f676,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK2,k1_relat_1(sK3)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl4_49 | spl4_69)),
% 0.21/0.51    inference(resolution,[],[f673,f483])).
% 0.21/0.51  fof(f483,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X0,k1_relat_1(sK3)) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) ) | ~spl4_49),
% 0.21/0.51    inference(avatar_component_clause,[],[f482])).
% 0.21/0.51  fof(f673,plain,(
% 0.21/0.51    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_69),
% 0.21/0.51    inference(avatar_component_clause,[],[f672])).
% 0.21/0.51  fof(f702,plain,(
% 0.21/0.51    ~spl4_7 | ~spl4_35 | ~spl4_40),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f701])).
% 0.21/0.51  fof(f701,plain,(
% 0.21/0.51    $false | (~spl4_7 | ~spl4_35 | ~spl4_40)),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f696])).
% 0.21/0.51  fof(f696,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl4_35 | ~spl4_40)),
% 0.21/0.51    inference(resolution,[],[f436,f368])).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f367])).
% 0.21/0.51  fof(f367,plain,(
% 0.21/0.51    spl4_35 <=> ! [X1,X0,X2] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.51  fof(f436,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl4_40),
% 0.21/0.51    inference(avatar_component_clause,[],[f435])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f684,plain,(
% 0.21/0.51    spl4_40 | ~spl4_6 | ~spl4_49 | ~spl4_61 | spl4_69),
% 0.21/0.51    inference(avatar_split_clause,[],[f682,f672,f608,f482,f107,f435])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl4_6 <=> r1_tarski(sK2,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f608,plain,(
% 0.21/0.51    spl4_61 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.21/0.51  fof(f682,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK2,sK0) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl4_49 | ~spl4_61 | spl4_69)),
% 0.21/0.51    inference(forward_demodulation,[],[f676,f609])).
% 0.21/0.51  fof(f609,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | ~spl4_61),
% 0.21/0.51    inference(avatar_component_clause,[],[f608])).
% 0.21/0.51  fof(f674,plain,(
% 0.21/0.51    ~spl4_7 | ~spl4_69 | spl4_3 | ~spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f666,f119,f96,f672,f111])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl4_9 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f666,plain,(
% 0.21/0.51    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_9)),
% 0.21/0.51    inference(superposition,[],[f97,f313])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_9),
% 0.21/0.51    inference(resolution,[],[f79,f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    v1_funct_1(sK3) | ~spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f631,plain,(
% 0.21/0.51    sK0 != k1_relat_1(sK3) | r1_tarski(sK2,k1_relat_1(sK3)) | ~r1_tarski(sK2,sK0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f630,plain,(
% 0.21/0.51    spl4_64 | ~spl4_5 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f614,f107,f103,f628])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl4_5 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f614,plain,(
% 0.21/0.51    r1_tarski(sK2,k1_xboole_0) | (~spl4_5 | ~spl4_6)),
% 0.21/0.51    inference(superposition,[],[f108,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f103])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    r1_tarski(sK2,sK0) | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f107])).
% 0.21/0.51  fof(f610,plain,(
% 0.21/0.51    ~spl4_7 | spl4_4 | spl4_61 | ~spl4_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f602,f115,f608,f100,f111])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl4_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.51  fof(f602,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_8),
% 0.21/0.51    inference(resolution,[],[f400,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,sK1) | ~spl4_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (~v1_funct_2(X5,X3,X4) | k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f397])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.51    inference(superposition,[],[f73,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f484,plain,(
% 0.21/0.51    ~spl4_18 | spl4_49 | ~spl4_48),
% 0.21/0.51    inference(avatar_split_clause,[],[f479,f475,f482,f190])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    spl4_18 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.51  fof(f475,plain,(
% 0.21/0.51    spl4_48 <=> ! [X1,X0,X2] : (~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.51  fof(f479,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(X0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) ) | ~spl4_48),
% 0.21/0.51    inference(superposition,[],[f476,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  % (5440)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.51  fof(f476,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X2))) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl4_48),
% 0.21/0.51    inference(avatar_component_clause,[],[f475])).
% 0.21/0.51  fof(f477,plain,(
% 0.21/0.51    ~spl4_18 | spl4_48 | ~spl4_38),
% 0.21/0.51    inference(avatar_split_clause,[],[f472,f407,f475,f190])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    spl4_38 <=> ! [X1,X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.51  fof(f472,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X2))) | ~v1_relat_1(sK3)) ) | ~spl4_38),
% 0.21/0.51    inference(resolution,[],[f410,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.51  fof(f410,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(k7_relat_1(sK3,X0)) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1)))) ) | ~spl4_38),
% 0.21/0.51    inference(resolution,[],[f408,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f72,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1)))) ) | ~spl4_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f407])).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    spl4_46),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f463])).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    $false | spl4_46),
% 0.21/0.51    inference(resolution,[],[f460,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.51  fof(f460,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK3))) | spl4_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f459])).
% 0.21/0.51  fof(f459,plain,(
% 0.21/0.51    spl4_46 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.51  fof(f461,plain,(
% 0.21/0.51    ~spl4_46 | spl4_44),
% 0.21/0.51    inference(avatar_split_clause,[],[f457,f448,f459])).
% 0.21/0.51  fof(f448,plain,(
% 0.21/0.51    spl4_44 <=> r1_tarski(k1_xboole_0,k1_relat_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.51  fof(f457,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK3))) | spl4_44),
% 0.21/0.51    inference(resolution,[],[f449,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f449,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | spl4_44),
% 0.21/0.51    inference(avatar_component_clause,[],[f448])).
% 0.21/0.51  fof(f440,plain,(
% 0.21/0.51    spl4_40 | ~spl4_41 | spl4_34 | ~spl4_39),
% 0.21/0.51    inference(avatar_split_clause,[],[f432,f425,f346,f438,f435])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    spl4_34 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.51  fof(f425,plain,(
% 0.21/0.51    spl4_39 <=> ! [X1,X0,X2] : (~r1_tarski(X0,k1_relat_1(sK3)) | v1_funct_2(k7_relat_1(sK3,X0),X0,X2) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.51  fof(f432,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK2,k1_relat_1(sK3)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (spl4_34 | ~spl4_39)),
% 0.21/0.51    inference(resolution,[],[f426,f347])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f346])).
% 0.21/0.51  fof(f426,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(k7_relat_1(sK3,X0),X0,X2) | ~r1_tarski(X0,k1_relat_1(sK3)) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl4_39),
% 0.21/0.51    inference(avatar_component_clause,[],[f425])).
% 0.21/0.51  fof(f427,plain,(
% 0.21/0.51    ~spl4_18 | spl4_39 | ~spl4_37),
% 0.21/0.51    inference(avatar_split_clause,[],[f422,f391,f425,f190])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    spl4_37 <=> ! [X1,X0] : (~r1_tarski(X0,k1_relat_1(sK3)) | v1_funct_2(k7_relat_1(sK3,X0),X0,X1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.51  fof(f422,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_relat_1(sK3)) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(k7_relat_1(sK3,X0),X0,X2) | ~v1_relat_1(sK3)) ) | ~spl4_37),
% 0.21/0.51    inference(resolution,[],[f394,f57])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(k7_relat_1(sK3,X0)) | ~r1_tarski(X0,k1_relat_1(sK3)) | ~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_2(k7_relat_1(sK3,X0),X0,X1)) ) | ~spl4_37),
% 0.21/0.51    inference(resolution,[],[f392,f155])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) | v1_funct_2(k7_relat_1(sK3,X0),X0,X1) | ~r1_tarski(X0,k1_relat_1(sK3))) ) | ~spl4_37),
% 0.21/0.51    inference(avatar_component_clause,[],[f391])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    ~spl4_18 | spl4_38 | ~spl4_33),
% 0.21/0.51    inference(avatar_split_clause,[],[f404,f342,f407,f190])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    spl4_33 <=> ! [X12] : v1_funct_1(k7_relat_1(sK3,X12))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.51  fof(f404,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) | ~v1_relat_1(sK3)) ) | ~spl4_33),
% 0.21/0.51    inference(resolution,[],[f353,f57])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~v1_relat_1(k7_relat_1(sK3,X4)) | m1_subset_1(k7_relat_1(sK3,X4),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X4)),X5))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),X5)) ) | ~spl4_33),
% 0.21/0.51    inference(resolution,[],[f343,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    ( ! [X12] : (v1_funct_1(k7_relat_1(sK3,X12))) ) | ~spl4_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f342])).
% 0.21/0.51  fof(f393,plain,(
% 0.21/0.51    ~spl4_18 | spl4_37 | ~spl4_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f388,f385,f391,f190])).
% 0.21/0.51  fof(f385,plain,(
% 0.21/0.51    spl4_36 <=> ! [X1,X0] : (v1_funct_2(k7_relat_1(sK3,X0),X0,X1) | ~r1_tarski(X0,k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) | ~v1_relat_1(k7_relat_1(sK3,X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.51  fof(f388,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) | v1_funct_2(k7_relat_1(sK3,X0),X0,X1) | ~v1_relat_1(sK3)) ) | ~spl4_36),
% 0.21/0.51    inference(resolution,[],[f386,f57])).
% 0.21/0.51  fof(f386,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK3,X0)) | ~r1_tarski(X0,k1_relat_1(sK3)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) | v1_funct_2(k7_relat_1(sK3,X0),X0,X1)) ) | ~spl4_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f385])).
% 0.21/0.51  fof(f387,plain,(
% 0.21/0.51    ~spl4_18 | spl4_36 | ~spl4_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f383,f334,f385,f190])).
% 0.21/0.51  fof(f334,plain,(
% 0.21/0.51    spl4_31 <=> ! [X3,X2] : (v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3) | ~v1_relat_1(k7_relat_1(sK3,X2)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_2(k7_relat_1(sK3,X0),X0,X1) | ~v1_relat_1(k7_relat_1(sK3,X0)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),X1) | ~r1_tarski(X0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) ) | ~spl4_31),
% 0.21/0.51    inference(superposition,[],[f335,f59])).
% 0.21/0.51  fof(f335,plain,(
% 0.21/0.51    ( ! [X2,X3] : (v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3) | ~v1_relat_1(k7_relat_1(sK3,X2)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3)) ) | ~spl4_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f334])).
% 0.21/0.51  fof(f369,plain,(
% 0.21/0.51    ~spl4_9 | spl4_35 | ~spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f364,f119,f367,f119])).
% 0.21/0.51  fof(f364,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3)) ) | ~spl4_9),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f361])).
% 0.21/0.51  % (5441)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  fof(f361,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_9),
% 0.21/0.51    inference(superposition,[],[f81,f313])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.51  fof(f351,plain,(
% 0.21/0.51    ~spl4_7 | ~spl4_30),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f349])).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    $false | (~spl4_7 | ~spl4_30)),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f332])).
% 0.21/0.51  fof(f332,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f331])).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    spl4_30 <=> ! [X1,X0] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.51  fof(f348,plain,(
% 0.21/0.51    ~spl4_7 | ~spl4_34 | spl4_2 | ~spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f326,f119,f93,f346,f111])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_2 | ~spl4_9)),
% 0.21/0.51    inference(superposition,[],[f94,f313])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    spl4_30 | spl4_33 | ~spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f327,f119,f342,f331])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    ( ! [X12,X10,X11] : (v1_funct_1(k7_relat_1(sK3,X12)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) ) | ~spl4_9),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f325])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    ( ! [X12,X10,X11] : (v1_funct_1(k7_relat_1(sK3,X12)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))) ) | ~spl4_9),
% 0.21/0.51    inference(superposition,[],[f269,f313])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_1(k2_partfun1(X0,X1,sK3,X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_9),
% 0.21/0.51    inference(resolution,[],[f80,f120])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    spl4_30 | spl4_31 | ~spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f329,f119,f334,f331])).
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(k7_relat_1(sK3,X2))) ) | ~spl4_9),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f323])).
% 0.21/0.51  fof(f323,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_2(k7_relat_1(sK3,X2),k1_relat_1(k7_relat_1(sK3,X2)),X3) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X2)),X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(k7_relat_1(sK3,X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_9),
% 0.21/0.51    inference(superposition,[],[f272,f313])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    ( ! [X6,X8,X7,X9] : (v1_funct_2(k2_partfun1(X6,X7,sK3,X8),k1_relat_1(k2_partfun1(X6,X7,sK3,X8)),X9) | ~r1_tarski(k2_relat_1(k2_partfun1(X6,X7,sK3,X8)),X9) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_relat_1(k2_partfun1(X6,X7,sK3,X8))) ) | ~spl4_9),
% 0.21/0.51    inference(resolution,[],[f269,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    ~spl4_7 | spl4_1 | ~spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f270,f119,f90,f111])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_1 | ~spl4_9)),
% 0.21/0.51    inference(resolution,[],[f269,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ~spl4_7 | spl4_18),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.51  % (5437)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    $false | (~spl4_7 | spl4_18)),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f196])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_18),
% 0.21/0.51    inference(resolution,[],[f191,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    ~v1_relat_1(sK3) | spl4_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f190])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl4_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f48,f119])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    v1_funct_1(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f18])).
% 0.21/0.52  fof(f18,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f49,f115])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl4_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f50,f111])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f107])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    r1_tarski(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ~spl4_4 | spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f52,f103,f100])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f53,f96,f93,f90])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (5428)------------------------------
% 0.21/0.52  % (5428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5428)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (5428)Memory used [KB]: 11129
% 0.21/0.52  % (5428)Time elapsed: 0.040 s
% 0.21/0.52  % (5428)------------------------------
% 0.21/0.52  % (5428)------------------------------
% 0.21/0.52  % (5431)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (5442)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (5421)Success in time 0.159 s
%------------------------------------------------------------------------------
