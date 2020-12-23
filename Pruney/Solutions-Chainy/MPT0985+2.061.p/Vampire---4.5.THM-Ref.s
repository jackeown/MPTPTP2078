%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 321 expanded)
%              Number of leaves         :   43 ( 130 expanded)
%              Depth                    :    9
%              Number of atoms          :  536 ( 965 expanded)
%              Number of equality atoms :  105 ( 186 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1073,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f115,f131,f137,f142,f155,f168,f188,f195,f211,f241,f257,f273,f319,f343,f352,f391,f427,f445,f571,f753,f768,f772,f876,f935,f982,f1009,f1019,f1065,f1072])).

fof(f1072,plain,
    ( spl4_17
    | ~ spl4_53 ),
    inference(avatar_contradiction_clause,[],[f1071])).

fof(f1071,plain,
    ( $false
    | spl4_17
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f1070,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1070,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_17
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f1069,f100])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1069,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
    | spl4_17
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f240,f767])).

fof(f767,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f765])).

fof(f765,plain,
    ( spl4_53
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f240,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl4_17
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1065,plain,
    ( spl4_26
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f995,f954,f327])).

fof(f327,plain,
    ( spl4_26
  <=> v1_xboole_0(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f954,plain,
    ( spl4_63
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f995,plain,
    ( v1_xboole_0(k2_funct_1(sK2))
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f994,f59])).

fof(f994,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_funct_1(sK2))
    | ~ spl4_63 ),
    inference(resolution,[],[f955,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f955,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f954])).

fof(f1019,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_funct_1(sK2)
    | k1_xboole_0 != sK0
    | k1_xboole_0 != sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1009,plain,
    ( spl4_7
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(avatar_contradiction_clause,[],[f1008])).

fof(f1008,plain,
    ( $false
    | spl4_7
    | ~ spl4_29
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f985,f955])).

fof(f985,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_7
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f984,f100])).

fof(f984,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_7
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f159,f342])).

fof(f342,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl4_29
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f159,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_7
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f982,plain,
    ( ~ spl4_25
    | ~ spl4_29
    | spl4_63 ),
    inference(avatar_contradiction_clause,[],[f981])).

fof(f981,plain,
    ( $false
    | ~ spl4_25
    | ~ spl4_29
    | spl4_63 ),
    inference(subsumption_resolution,[],[f980,f956])).

fof(f956,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_63 ),
    inference(avatar_component_clause,[],[f954])).

fof(f980,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_25
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f972,f100])).

fof(f972,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl4_25
    | ~ spl4_29 ),
    inference(superposition,[],[f318,f342])).

fof(f318,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl4_25
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f935,plain,
    ( spl4_36
    | ~ spl4_53 ),
    inference(avatar_contradiction_clause,[],[f934])).

fof(f934,plain,
    ( $false
    | spl4_36
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f929,f59])).

fof(f929,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_36
    | ~ spl4_53 ),
    inference(superposition,[],[f444,f767])).

fof(f444,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl4_36
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f876,plain,
    ( k1_xboole_0 != k2_funct_1(sK2)
    | k1_xboole_0 != sK0
    | sK0 != k1_relat_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | sK1 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f772,plain,
    ( ~ spl4_7
    | ~ spl4_19
    | spl4_52 ),
    inference(avatar_contradiction_clause,[],[f771])).

fof(f771,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_19
    | spl4_52 ),
    inference(subsumption_resolution,[],[f770,f158])).

fof(f158,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f157])).

fof(f770,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_19
    | spl4_52 ),
    inference(subsumption_resolution,[],[f769,f256])).

fof(f256,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl4_19
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f769,plain,
    ( sK1 != k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_52 ),
    inference(superposition,[],[f763,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f763,plain,
    ( sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | spl4_52 ),
    inference(avatar_component_clause,[],[f761])).

fof(f761,plain,
    ( spl4_52
  <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f768,plain,
    ( ~ spl4_52
    | spl4_53
    | ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f759,f161,f157,f765,f761])).

fof(f161,plain,
    ( spl4_8
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f759,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_7
    | spl4_8 ),
    inference(subsumption_resolution,[],[f182,f158])).

fof(f182,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_8 ),
    inference(resolution,[],[f163,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f163,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f161])).

fof(f753,plain,
    ( spl4_50
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f630,f327,f750])).

fof(f750,plain,
    ( spl4_50
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f630,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl4_26 ),
    inference(resolution,[],[f329,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f329,plain,
    ( v1_xboole_0(k2_funct_1(sK2))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f327])).

fof(f571,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_relat_1(sK2)
    | sK1 = k2_relat_1(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f445,plain,
    ( ~ spl4_36
    | ~ spl4_7
    | spl4_26 ),
    inference(avatar_split_clause,[],[f439,f327,f157,f442])).

fof(f439,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl4_7
    | spl4_26 ),
    inference(subsumption_resolution,[],[f436,f328])).

fof(f328,plain,
    ( ~ v1_xboole_0(k2_funct_1(sK2))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f327])).

fof(f436,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(resolution,[],[f158,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f427,plain,
    ( spl4_34
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f408,f174,f424])).

fof(f424,plain,
    ( spl4_34
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f174,plain,
    ( spl4_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f408,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_10 ),
    inference(resolution,[],[f176,f61])).

fof(f176,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f391,plain,
    ( sK0 != k1_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f352,plain,
    ( spl4_30
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f346,f336,f134,f349])).

fof(f349,plain,
    ( spl4_30
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f134,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f336,plain,
    ( spl4_28
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f346,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f344,f136])).

fof(f136,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f344,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_28 ),
    inference(superposition,[],[f338,f89])).

fof(f338,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f336])).

fof(f343,plain,
    ( spl4_28
    | spl4_29
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f325,f134,f128,f340,f336])).

fof(f128,plain,
    ( spl4_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f325,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f132,f136])).

fof(f132,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(resolution,[],[f130,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f130,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f319,plain,
    ( spl4_25
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_19
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f313,f270,f254,f185,f165,f316])).

fof(f165,plain,
    ( spl4_9
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f185,plain,
    ( spl4_12
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f270,plain,
    ( spl4_21
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f313,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_19
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f312,f256])).

fof(f312,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f201,f272])).

fof(f272,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f270])).

fof(f201,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f198,f187])).

fof(f187,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f198,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl4_9 ),
    inference(resolution,[],[f166,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f166,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f273,plain,
    ( spl4_21
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f263,f152,f112,f107,f270])).

fof(f107,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f112,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f152,plain,
    ( spl4_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f263,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f126,f154])).

fof(f154,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f126,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f122,f109])).

fof(f109,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f122,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f114,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f114,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f257,plain,
    ( spl4_19
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f248,f208,f152,f112,f107,f254])).

fof(f208,plain,
    ( spl4_14
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f248,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f247,f210])).

fof(f210,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f208])).

fof(f247,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f125,f154])).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f121,f109])).

fof(f121,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f114,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f241,plain,
    ( ~ spl4_17
    | ~ spl4_4
    | spl4_10 ),
    inference(avatar_split_clause,[],[f236,f174,f134,f238])).

fof(f236,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_4
    | spl4_10 ),
    inference(subsumption_resolution,[],[f146,f175])).

fof(f175,plain,
    ( ~ v1_xboole_0(sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f146,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f136,f62])).

fof(f211,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f149,f139,f134,f208])).

fof(f139,plain,
    ( spl4_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f149,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f147,f136])).

fof(f147,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(superposition,[],[f141,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f141,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f195,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | spl4_9 ),
    inference(subsumption_resolution,[],[f193,f167])).

fof(f167,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f193,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f117,f154])).

fof(f117,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f109,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f188,plain,
    ( spl4_12
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f183,f152,f107,f185])).

fof(f183,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f116,f154])).

fof(f116,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f109,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f168,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f53,f165,f161,f157])).

fof(f53,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f155,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f143,f134,f152])).

fof(f143,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f136,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f142,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f58,f139])).

fof(f58,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f137,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f56,f134])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f131,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f55,f128])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f115,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f57,f112])).

fof(f57,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f54,f107])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:06:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (12400)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (12400)Refutation not found, incomplete strategy% (12400)------------------------------
% 0.21/0.47  % (12400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12400)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (12400)Memory used [KB]: 1791
% 0.21/0.47  % (12400)Time elapsed: 0.052 s
% 0.21/0.47  % (12400)------------------------------
% 0.21/0.47  % (12400)------------------------------
% 0.21/0.48  % (12388)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (12388)Refutation not found, incomplete strategy% (12388)------------------------------
% 0.21/0.48  % (12388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12388)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (12388)Memory used [KB]: 10618
% 0.21/0.48  % (12388)Time elapsed: 0.062 s
% 0.21/0.48  % (12388)------------------------------
% 0.21/0.48  % (12388)------------------------------
% 0.21/0.49  % (12398)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (12387)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (12389)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (12391)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (12395)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (12405)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (12406)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (12401)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (12390)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (12396)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (12399)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (12404)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (12393)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (12390)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1073,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f110,f115,f131,f137,f142,f155,f168,f188,f195,f211,f241,f257,f273,f319,f343,f352,f391,f427,f445,f571,f753,f768,f772,f876,f935,f982,f1009,f1019,f1065,f1072])).
% 0.21/0.51  fof(f1072,plain,(
% 0.21/0.51    spl4_17 | ~spl4_53),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1071])).
% 0.21/0.51  fof(f1071,plain,(
% 0.21/0.51    $false | (spl4_17 | ~spl4_53)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1070,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f1070,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | (spl4_17 | ~spl4_53)),
% 0.21/0.51    inference(forward_demodulation,[],[f1069,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f1069,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) | (spl4_17 | ~spl4_53)),
% 0.21/0.51    inference(forward_demodulation,[],[f240,f767])).
% 0.21/0.51  fof(f767,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl4_53),
% 0.21/0.51    inference(avatar_component_clause,[],[f765])).
% 0.21/0.51  fof(f765,plain,(
% 0.21/0.51    spl4_53 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f238])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    spl4_17 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.51  fof(f1065,plain,(
% 0.21/0.51    spl4_26 | ~spl4_63),
% 0.21/0.51    inference(avatar_split_clause,[],[f995,f954,f327])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    spl4_26 <=> v1_xboole_0(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.51  fof(f954,plain,(
% 0.21/0.51    spl4_63 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.21/0.51  fof(f995,plain,(
% 0.21/0.51    v1_xboole_0(k2_funct_1(sK2)) | ~spl4_63),
% 0.21/0.51    inference(subsumption_resolution,[],[f994,f59])).
% 0.21/0.51  fof(f994,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_funct_1(sK2)) | ~spl4_63),
% 0.21/0.51    inference(resolution,[],[f955,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.51  fof(f955,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl4_63),
% 0.21/0.51    inference(avatar_component_clause,[],[f954])).
% 0.21/0.51  fof(f1019,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | k1_xboole_0 != k2_funct_1(sK2) | k1_xboole_0 != sK0 | k1_xboole_0 != sK1 | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f1009,plain,(
% 0.21/0.51    spl4_7 | ~spl4_29 | ~spl4_63),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1008])).
% 0.21/0.51  fof(f1008,plain,(
% 0.21/0.51    $false | (spl4_7 | ~spl4_29 | ~spl4_63)),
% 0.21/0.51    inference(subsumption_resolution,[],[f985,f955])).
% 0.21/0.51  fof(f985,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_7 | ~spl4_29)),
% 0.21/0.51    inference(forward_demodulation,[],[f984,f100])).
% 0.21/0.51  fof(f984,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_7 | ~spl4_29)),
% 0.21/0.51    inference(forward_demodulation,[],[f159,f342])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl4_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f340])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    spl4_29 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl4_7 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.51  fof(f982,plain,(
% 0.21/0.51    ~spl4_25 | ~spl4_29 | spl4_63),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f981])).
% 0.21/0.51  fof(f981,plain,(
% 0.21/0.51    $false | (~spl4_25 | ~spl4_29 | spl4_63)),
% 0.21/0.51    inference(subsumption_resolution,[],[f980,f956])).
% 0.21/0.51  fof(f956,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | spl4_63),
% 0.21/0.51    inference(avatar_component_clause,[],[f954])).
% 0.21/0.51  fof(f980,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl4_25 | ~spl4_29)),
% 0.21/0.51    inference(forward_demodulation,[],[f972,f100])).
% 0.21/0.51  fof(f972,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | (~spl4_25 | ~spl4_29)),
% 0.21/0.51    inference(superposition,[],[f318,f342])).
% 0.21/0.51  fof(f318,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl4_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f316])).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    spl4_25 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.51  fof(f935,plain,(
% 0.21/0.51    spl4_36 | ~spl4_53),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f934])).
% 0.21/0.51  fof(f934,plain,(
% 0.21/0.51    $false | (spl4_36 | ~spl4_53)),
% 0.21/0.51    inference(subsumption_resolution,[],[f929,f59])).
% 0.21/0.51  fof(f929,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | (spl4_36 | ~spl4_53)),
% 0.21/0.51    inference(superposition,[],[f444,f767])).
% 0.21/0.51  fof(f444,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0) | spl4_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f442])).
% 0.21/0.51  fof(f442,plain,(
% 0.21/0.51    spl4_36 <=> v1_xboole_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.51  fof(f876,plain,(
% 0.21/0.51    k1_xboole_0 != k2_funct_1(sK2) | k1_xboole_0 != sK0 | sK0 != k1_relat_1(sK2) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | sK1 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f772,plain,(
% 0.21/0.51    ~spl4_7 | ~spl4_19 | spl4_52),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f771])).
% 0.21/0.51  fof(f771,plain,(
% 0.21/0.51    $false | (~spl4_7 | ~spl4_19 | spl4_52)),
% 0.21/0.51    inference(subsumption_resolution,[],[f770,f158])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f770,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_19 | spl4_52)),
% 0.21/0.51    inference(subsumption_resolution,[],[f769,f256])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f254])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    spl4_19 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.51  fof(f769,plain,(
% 0.21/0.51    sK1 != k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_52),
% 0.21/0.51    inference(superposition,[],[f763,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f763,plain,(
% 0.21/0.51    sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | spl4_52),
% 0.21/0.51    inference(avatar_component_clause,[],[f761])).
% 0.21/0.51  fof(f761,plain,(
% 0.21/0.51    spl4_52 <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.21/0.51  fof(f768,plain,(
% 0.21/0.51    ~spl4_52 | spl4_53 | ~spl4_7 | spl4_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f759,f161,f157,f765,f761])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl4_8 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.51  fof(f759,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_7 | spl4_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f182,f158])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_8),
% 0.21/0.51    inference(resolution,[],[f163,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f161])).
% 0.21/0.51  fof(f753,plain,(
% 0.21/0.51    spl4_50 | ~spl4_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f630,f327,f750])).
% 0.21/0.51  fof(f750,plain,(
% 0.21/0.51    spl4_50 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.21/0.51  fof(f630,plain,(
% 0.21/0.51    k1_xboole_0 = k2_funct_1(sK2) | ~spl4_26),
% 0.21/0.51    inference(resolution,[],[f329,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    v1_xboole_0(k2_funct_1(sK2)) | ~spl4_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f327])).
% 0.21/0.51  fof(f571,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | sK1 != k2_relat_1(sK2) | sK1 = k2_relat_1(k1_xboole_0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f445,plain,(
% 0.21/0.51    ~spl4_36 | ~spl4_7 | spl4_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f439,f327,f157,f442])).
% 0.21/0.51  fof(f439,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0) | (~spl4_7 | spl4_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f436,f328])).
% 0.21/0.51  fof(f328,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_funct_1(sK2)) | spl4_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f327])).
% 0.21/0.51  fof(f436,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0) | v1_xboole_0(k2_funct_1(sK2)) | ~spl4_7),
% 0.21/0.51    inference(resolution,[],[f158,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.51  fof(f427,plain,(
% 0.21/0.51    spl4_34 | ~spl4_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f408,f174,f424])).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    spl4_34 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl4_10 <=> v1_xboole_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl4_10),
% 0.21/0.51    inference(resolution,[],[f176,f61])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    v1_xboole_0(sK2) | ~spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f174])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    sK0 != k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f352,plain,(
% 0.21/0.51    spl4_30 | ~spl4_4 | ~spl4_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f346,f336,f134,f349])).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    spl4_30 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    spl4_28 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | (~spl4_4 | ~spl4_28)),
% 0.21/0.51    inference(subsumption_resolution,[],[f344,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f134])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_28),
% 0.21/0.51    inference(superposition,[],[f338,f89])).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f336])).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    spl4_28 | spl4_29 | ~spl4_3 | ~spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f325,f134,f128,f340,f336])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl4_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_3 | ~spl4_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f132,f136])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.21/0.51    inference(resolution,[],[f130,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl4_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f128])).
% 0.21/0.51  fof(f319,plain,(
% 0.21/0.51    spl4_25 | ~spl4_9 | ~spl4_12 | ~spl4_19 | ~spl4_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f313,f270,f254,f185,f165,f316])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl4_9 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    spl4_12 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    spl4_21 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl4_9 | ~spl4_12 | ~spl4_19 | ~spl4_21)),
% 0.21/0.51    inference(forward_demodulation,[],[f312,f256])).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl4_9 | ~spl4_12 | ~spl4_21)),
% 0.21/0.51    inference(forward_demodulation,[],[f201,f272])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f270])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl4_9 | ~spl4_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f198,f187])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK2)) | ~spl4_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f185])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl4_9),
% 0.21/0.51    inference(resolution,[],[f166,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    v1_funct_1(k2_funct_1(sK2)) | ~spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f165])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    spl4_21 | ~spl4_1 | ~spl4_2 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f263,f152,f112,f107,f270])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl4_1 <=> v1_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl4_2 <=> v2_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl4_6 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f126,f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl4_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f152])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f122,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    v1_funct_1(sK2) | ~spl4_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f107])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_2),
% 0.21/0.51    inference(resolution,[],[f114,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    v2_funct_1(sK2) | ~spl4_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f112])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    spl4_19 | ~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f248,f208,f152,f112,f107,f254])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    spl4_14 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f247,f210])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2) | ~spl4_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f208])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f125,f154])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f121,f109])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_2),
% 0.21/0.51    inference(resolution,[],[f114,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    ~spl4_17 | ~spl4_4 | spl4_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f236,f174,f134,f238])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | (~spl4_4 | spl4_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f146,f175])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2) | spl4_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f174])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK2) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f136,f62])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    spl4_14 | ~spl4_4 | ~spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f149,f139,f134,f208])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl4_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2) | (~spl4_4 | ~spl4_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f147,f136])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_5),
% 0.21/0.51    inference(superposition,[],[f141,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f139])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    ~spl4_1 | ~spl4_6 | spl4_9),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f194])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    $false | (~spl4_1 | ~spl4_6 | spl4_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f193,f167])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~v1_funct_1(k2_funct_1(sK2)) | spl4_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f165])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    v1_funct_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f117,f154])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl4_1),
% 0.21/0.51    inference(resolution,[],[f109,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    spl4_12 | ~spl4_1 | ~spl4_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f183,f152,f107,f185])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f116,f154])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 0.21/0.51    inference(resolution,[],[f109,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ~spl4_7 | ~spl4_8 | ~spl4_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f53,f165,f161,f157])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f24])).
% 0.21/0.51  fof(f24,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    spl4_6 | ~spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f143,f134,f152])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl4_4),
% 0.21/0.51    inference(resolution,[],[f136,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl4_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f58,f139])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl4_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f134])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl4_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f55,f128])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl4_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f57,f112])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl4_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f107])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12390)------------------------------
% 0.21/0.51  % (12390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12390)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12390)Memory used [KB]: 11001
% 0.21/0.51  % (12390)Time elapsed: 0.089 s
% 0.21/0.51  % (12390)------------------------------
% 0.21/0.51  % (12390)------------------------------
% 1.15/0.51  % (12386)Success in time 0.142 s
%------------------------------------------------------------------------------
