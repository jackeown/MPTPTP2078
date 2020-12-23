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
% DateTime   : Thu Dec  3 13:03:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  235 ( 453 expanded)
%              Number of leaves         :   63 ( 188 expanded)
%              Depth                    :   11
%              Number of atoms          :  711 (1505 expanded)
%              Number of equality atoms :  146 ( 337 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f122,f126,f130,f134,f138,f146,f150,f166,f205,f208,f230,f232,f243,f324,f369,f378,f411,f429,f492,f704,f708,f736,f746,f789,f797,f804,f807,f852,f868,f887,f1054,f1055,f1153,f1154,f1156,f1214,f1218,f1220])).

fof(f1220,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK0
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1218,plain,
    ( k1_xboole_0 != sK3
    | sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | sK2 = k1_relat_1(k7_relat_1(k1_xboole_0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1214,plain,
    ( spl4_103
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f1210,f1172,f164,f148,f1212])).

fof(f1212,plain,
    ( spl4_103
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).

fof(f148,plain,
    ( spl4_12
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f164,plain,
    ( spl4_15
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1172,plain,
    ( spl4_96
  <=> sK2 = k1_relat_1(k7_relat_1(k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f1210,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_96 ),
    inference(forward_demodulation,[],[f1209,f149])).

fof(f149,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f1209,plain,
    ( k1_relat_1(k1_xboole_0) = sK2
    | ~ spl4_15
    | ~ spl4_96 ),
    inference(forward_demodulation,[],[f1173,f212])).

fof(f212,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_15 ),
    inference(resolution,[],[f210,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f210,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X4) )
    | ~ spl4_15 ),
    inference(resolution,[],[f181,f165])).

fof(f165,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f78,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f1173,plain,
    ( sK2 = k1_relat_1(k7_relat_1(k1_xboole_0,sK2))
    | ~ spl4_96 ),
    inference(avatar_component_clause,[],[f1172])).

fof(f1156,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK0
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1154,plain,
    ( k1_xboole_0 != sK1
    | r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1153,plain,
    ( ~ spl4_59
    | ~ spl4_65 ),
    inference(avatar_contradiction_clause,[],[f1149])).

fof(f1149,plain,
    ( $false
    | ~ spl4_59
    | ~ spl4_65 ),
    inference(resolution,[],[f788,f735])).

fof(f735,plain,
    ( ! [X11] : m1_subset_1(k7_relat_1(sK3,X11),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f734])).

fof(f734,plain,
    ( spl4_59
  <=> ! [X11] : m1_subset_1(k7_relat_1(sK3,X11),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f788,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f787])).

fof(f787,plain,
    ( spl4_65
  <=> ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1055,plain,
    ( sK0 != k1_relat_1(sK3)
    | r1_tarski(sK2,k1_relat_1(sK3))
    | ~ r1_tarski(sK2,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1054,plain,
    ( ~ spl4_7
    | spl4_4
    | spl4_85
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f1046,f132,f1052,f117,f128])).

fof(f128,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f117,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1052,plain,
    ( spl4_85
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f132,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1046,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_8 ),
    inference(resolution,[],[f575,f133])).

fof(f133,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f575,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X5,X3,X4)
      | k1_relat_1(X5) = X3
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f572])).

fof(f572,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f88,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f887,plain,
    ( spl4_76
    | ~ spl4_22
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f874,f850,f228,f884])).

fof(f884,plain,
    ( spl4_76
  <=> k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f228,plain,
    ( spl4_22
  <=> ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f850,plain,
    ( spl4_74
  <=> m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f874,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl4_22
    | ~ spl4_74 ),
    inference(resolution,[],[f851,f245])).

fof(f245,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X2 )
    | ~ spl4_22 ),
    inference(resolution,[],[f229,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f229,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f228])).

fof(f851,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f850])).

fof(f868,plain,
    ( ~ spl4_59
    | ~ spl4_73 ),
    inference(avatar_contradiction_clause,[],[f863])).

fof(f863,plain,
    ( $false
    | ~ spl4_59
    | ~ spl4_73 ),
    inference(resolution,[],[f848,f735])).

fof(f848,plain,
    ( ! [X14,X13] : ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f847])).

fof(f847,plain,
    ( spl4_73
  <=> ! [X13,X14] : ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f852,plain,
    ( spl4_73
    | spl4_74
    | ~ spl4_21
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f837,f322,f222,f850,f847])).

fof(f222,plain,
    ( spl4_21
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f322,plain,
    ( spl4_24
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f837,plain,
    ( ! [X14,X13] :
        ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
    | ~ spl4_24 ),
    inference(superposition,[],[f449,f323])).

fof(f323,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f322])).

fof(f449,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
      | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X3))) ) ),
    inference(superposition,[],[f95,f100])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f807,plain,
    ( ~ spl4_18
    | ~ spl4_60
    | spl4_67 ),
    inference(avatar_split_clause,[],[f806,f802,f748,f193])).

fof(f193,plain,
    ( spl4_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f748,plain,
    ( spl4_60
  <=> r1_tarski(sK2,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f802,plain,
    ( spl4_67
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f806,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_67 ),
    inference(trivial_inequality_removal,[],[f805])).

fof(f805,plain,
    ( sK2 != sK2
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_67 ),
    inference(superposition,[],[f803,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f803,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_67 ),
    inference(avatar_component_clause,[],[f802])).

fof(f804,plain,
    ( ~ spl4_52
    | ~ spl4_67
    | spl4_66 ),
    inference(avatar_split_clause,[],[f799,f792,f802,f706])).

fof(f706,plain,
    ( spl4_52
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f792,plain,
    ( spl4_66
  <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f799,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_66 ),
    inference(superposition,[],[f793,f85])).

fof(f793,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_66 ),
    inference(avatar_component_clause,[],[f792])).

fof(f797,plain,
    ( ~ spl4_52
    | spl4_4
    | ~ spl4_66
    | spl4_51 ),
    inference(avatar_split_clause,[],[f741,f702,f792,f117,f706])).

fof(f702,plain,
    ( spl4_51
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f741,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_51 ),
    inference(resolution,[],[f703,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f703,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_51 ),
    inference(avatar_component_clause,[],[f702])).

fof(f789,plain,
    ( spl4_65
    | ~ spl4_53
    | spl4_52 ),
    inference(avatar_split_clause,[],[f766,f706,f710,f787])).

fof(f710,plain,
    ( spl4_53
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f766,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl4_52 ),
    inference(resolution,[],[f707,f95])).

fof(f707,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_52 ),
    inference(avatar_component_clause,[],[f706])).

fof(f746,plain,
    ( ~ spl4_18
    | spl4_53 ),
    inference(avatar_split_clause,[],[f742,f710,f193])).

fof(f742,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_53 ),
    inference(resolution,[],[f711,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f711,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_53 ),
    inference(avatar_component_clause,[],[f710])).

fof(f736,plain,
    ( ~ spl4_9
    | ~ spl4_7
    | spl4_59
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f700,f136,f128,f734,f128,f136])).

fof(f136,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f700,plain,
    ( ! [X11] :
        ( m1_subset_1(k7_relat_1(sK3,X11),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(superposition,[],[f98,f672])).

fof(f672,plain,
    ( ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f493,f129])).

fof(f129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f493,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_9 ),
    inference(resolution,[],[f96,f137])).

fof(f137,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f708,plain,
    ( ~ spl4_52
    | spl4_3
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f689,f136,f128,f113,f706])).

fof(f113,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f689,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(superposition,[],[f114,f672])).

fof(f114,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f704,plain,
    ( ~ spl4_51
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f688,f136,f128,f110,f702])).

fof(f110,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f688,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(superposition,[],[f111,f672])).

fof(f111,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f492,plain,
    ( ~ spl4_37
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f483,f409,f128,f490])).

% (862)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f490,plain,
    ( spl4_37
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f409,plain,
    ( spl4_30
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f483,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(resolution,[],[f410,f129])).

fof(f410,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f409])).

fof(f429,plain,
    ( spl4_32
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f416,f376,f228,f426])).

fof(f426,plain,
    ( spl4_32
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f376,plain,
    ( spl4_27
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f416,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(resolution,[],[f377,f245])).

fof(f377,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f376])).

fof(f411,plain,
    ( ~ spl4_18
    | spl4_30
    | spl4_26 ),
    inference(avatar_split_clause,[],[f403,f373,f409,f193])).

fof(f373,plain,
    ( spl4_26
  <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f403,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_relat_1(sK3) )
    | spl4_26 ),
    inference(resolution,[],[f380,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f87,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f380,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),X1)
        | ~ r1_tarski(X1,k1_xboole_0) )
    | spl4_26 ),
    inference(resolution,[],[f374,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f374,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f373])).

fof(f378,plain,
    ( ~ spl4_26
    | spl4_27
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f371,f367,f376,f373])).

fof(f367,plain,
    ( spl4_25
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f371,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ spl4_25 ),
    inference(superposition,[],[f368,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f368,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ r1_tarski(k2_relat_1(sK3),X0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f367])).

fof(f369,plain,
    ( ~ spl4_18
    | spl4_25
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f363,f136,f367,f193])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl4_9 ),
    inference(resolution,[],[f77,f137])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

% (866)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f324,plain,
    ( spl4_24
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f316,f228,f128,f322])).

fof(f316,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(resolution,[],[f297,f129])).

fof(f297,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0)) )
    | ~ spl4_22 ),
    inference(resolution,[],[f260,f69])).

% (864)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f260,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
        | k1_xboole_0 = k1_relat_1(k7_relat_1(X2,k1_xboole_0)) )
    | ~ spl4_22 ),
    inference(resolution,[],[f251,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f251,plain,
    ( ! [X8] :
        ( ~ v1_relat_1(X8)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(X8,k1_xboole_0)) )
    | ~ spl4_22 ),
    inference(resolution,[],[f229,f70])).

fof(f243,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f239,f136,f107,f128])).

fof(f107,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f239,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_9 ),
    inference(resolution,[],[f238,f108])).

fof(f108,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_9 ),
    inference(resolution,[],[f97,f137])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f232,plain,
    ( ~ spl4_15
    | spl4_21
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f231,f164,f144,f222,f164])).

fof(f144,plain,
    ( spl4_11
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f231,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f218,f145])).

fof(f145,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f218,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl4_15 ),
    inference(superposition,[],[f71,f212])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f230,plain,
    ( ~ spl4_15
    | spl4_22
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f226,f164,f148,f228,f164])).

fof(f226,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f225,f149])).

fof(f225,plain,
    ( ! [X1] :
        ( k1_xboole_0 = X1
        | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f217,f149])).

fof(f217,plain,
    ( ! [X1] :
        ( k1_relat_1(k1_xboole_0) = X1
        | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_15 ),
    inference(superposition,[],[f72,f212])).

fof(f208,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl4_20 ),
    inference(resolution,[],[f204,f69])).

fof(f204,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl4_20
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f205,plain,
    ( ~ spl4_20
    | ~ spl4_7
    | spl4_18 ),
    inference(avatar_split_clause,[],[f200,f193,f128,f203])).

fof(f200,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_7
    | spl4_18 ),
    inference(resolution,[],[f199,f129])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_18 ),
    inference(resolution,[],[f194,f68])).

fof(f194,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f193])).

fof(f166,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f162,f164])).

fof(f162,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f69,f99])).

fof(f150,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f65,f148])).

fof(f65,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f146,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f66,f144])).

fof(f66,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f138,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f58,f136])).

fof(f58,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f51])).

fof(f51,plain,
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

% (868)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f134,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f59,f132])).

fof(f59,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f130,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f60,f128])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f126,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f61,f124])).

fof(f124,plain,
    ( spl4_6
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f61,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f122,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f62,f120,f117])).

fof(f120,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f62,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f115,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f63,f113,f110,f107])).

fof(f63,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:13:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (865)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (858)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (867)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (859)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (869)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (855)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (863)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (853)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (854)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (871)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (872)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (852)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (857)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (870)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (856)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (861)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (858)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (860)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1221,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f115,f122,f126,f130,f134,f138,f146,f150,f166,f205,f208,f230,f232,f243,f324,f369,f378,f411,f429,f492,f704,f708,f736,f746,f789,f797,f804,f807,f852,f868,f887,f1054,f1055,f1153,f1154,f1156,f1214,f1218,f1220])).
% 0.21/0.52  fof(f1220,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != sK0 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f1218,plain,(
% 0.21/0.52    k1_xboole_0 != sK3 | sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | sK2 = k1_relat_1(k7_relat_1(k1_xboole_0,sK2))),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f1214,plain,(
% 0.21/0.52    spl4_103 | ~spl4_12 | ~spl4_15 | ~spl4_96),
% 0.21/0.52    inference(avatar_split_clause,[],[f1210,f1172,f164,f148,f1212])).
% 0.21/0.52  fof(f1212,plain,(
% 0.21/0.52    spl4_103 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl4_12 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    spl4_15 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.52  fof(f1172,plain,(
% 0.21/0.52    spl4_96 <=> sK2 = k1_relat_1(k7_relat_1(k1_xboole_0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 0.21/0.52  fof(f1210,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | (~spl4_12 | ~spl4_15 | ~spl4_96)),
% 0.21/0.52    inference(forward_demodulation,[],[f1209,f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f148])).
% 0.21/0.52  fof(f1209,plain,(
% 0.21/0.52    k1_relat_1(k1_xboole_0) = sK2 | (~spl4_15 | ~spl4_96)),
% 0.21/0.52    inference(forward_demodulation,[],[f1173,f212])).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl4_15),
% 0.21/0.52    inference(resolution,[],[f210,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X4)) ) | ~spl4_15),
% 0.21/0.52    inference(resolution,[],[f181,f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    v1_relat_1(k1_xboole_0) | ~spl4_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f164])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.52    inference(resolution,[],[f78,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f1173,plain,(
% 0.21/0.52    sK2 = k1_relat_1(k7_relat_1(k1_xboole_0,sK2)) | ~spl4_96),
% 0.21/0.52    inference(avatar_component_clause,[],[f1172])).
% 0.21/0.52  fof(f1156,plain,(
% 0.21/0.52    k1_xboole_0 != sK3 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != sK0 | sK0 = k1_relat_1(sK3)),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f1154,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | r1_tarski(sK1,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f1153,plain,(
% 0.21/0.52    ~spl4_59 | ~spl4_65),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1149])).
% 0.21/0.52  fof(f1149,plain,(
% 0.21/0.52    $false | (~spl4_59 | ~spl4_65)),
% 0.21/0.52    inference(resolution,[],[f788,f735])).
% 0.21/0.52  fof(f735,plain,(
% 0.21/0.52    ( ! [X11] : (m1_subset_1(k7_relat_1(sK3,X11),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_59),
% 0.21/0.52    inference(avatar_component_clause,[],[f734])).
% 0.21/0.52  fof(f734,plain,(
% 0.21/0.52    spl4_59 <=> ! [X11] : m1_subset_1(k7_relat_1(sK3,X11),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 0.21/0.52  fof(f788,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl4_65),
% 0.21/0.52    inference(avatar_component_clause,[],[f787])).
% 0.21/0.52  fof(f787,plain,(
% 0.21/0.52    spl4_65 <=> ! [X0] : ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.21/0.52  fof(f1055,plain,(
% 0.21/0.52    sK0 != k1_relat_1(sK3) | r1_tarski(sK2,k1_relat_1(sK3)) | ~r1_tarski(sK2,sK0)),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f1054,plain,(
% 0.21/0.52    ~spl4_7 | spl4_4 | spl4_85 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f1046,f132,f1052,f117,f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f1052,plain,(
% 0.21/0.52    spl4_85 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl4_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.52  fof(f1046,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_8),
% 0.21/0.52    inference(resolution,[],[f575,f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    v1_funct_2(sK3,sK0,sK1) | ~spl4_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f132])).
% 0.21/0.52  fof(f575,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~v1_funct_2(X5,X3,X4) | k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f572])).
% 0.21/0.52  fof(f572,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.52    inference(superposition,[],[f88,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f887,plain,(
% 0.21/0.52    spl4_76 | ~spl4_22 | ~spl4_74),
% 0.21/0.52    inference(avatar_split_clause,[],[f874,f850,f228,f884])).
% 0.21/0.52  fof(f884,plain,(
% 0.21/0.52    spl4_76 <=> k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    spl4_22 <=> ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.52  fof(f850,plain,(
% 0.21/0.52    spl4_74 <=> m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 0.21/0.52  fof(f874,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) | (~spl4_22 | ~spl4_74)),
% 0.21/0.52    inference(resolution,[],[f851,f245])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X2) ) | ~spl4_22),
% 0.21/0.52    inference(resolution,[],[f229,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f229,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl4_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f228])).
% 0.21/0.52  fof(f851,plain,(
% 0.21/0.52    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl4_74),
% 0.21/0.52    inference(avatar_component_clause,[],[f850])).
% 0.21/0.52  fof(f868,plain,(
% 0.21/0.52    ~spl4_59 | ~spl4_73),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f863])).
% 0.21/0.52  fof(f863,plain,(
% 0.21/0.52    $false | (~spl4_59 | ~spl4_73)),
% 0.21/0.52    inference(resolution,[],[f848,f735])).
% 0.21/0.52  fof(f848,plain,(
% 0.21/0.52    ( ! [X14,X13] : (~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) ) | ~spl4_73),
% 0.21/0.52    inference(avatar_component_clause,[],[f847])).
% 0.21/0.52  fof(f847,plain,(
% 0.21/0.52    spl4_73 <=> ! [X13,X14] : ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 0.21/0.52  fof(f852,plain,(
% 0.21/0.52    spl4_73 | spl4_74 | ~spl4_21 | ~spl4_24),
% 0.21/0.52    inference(avatar_split_clause,[],[f837,f322,f222,f850,f847])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    spl4_21 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    spl4_24 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.52  fof(f837,plain,(
% 0.21/0.52    ( ! [X14,X13] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))) ) | ~spl4_24),
% 0.21/0.52    inference(superposition,[],[f449,f323])).
% 0.21/0.52  fof(f323,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | ~spl4_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f322])).
% 0.21/0.52  fof(f449,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~r1_tarski(k1_relat_1(X4),k1_xboole_0) | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X3)))) )),
% 0.21/0.52    inference(superposition,[],[f95,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.53    inference(flattening,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.53  fof(f807,plain,(
% 0.21/0.53    ~spl4_18 | ~spl4_60 | spl4_67),
% 0.21/0.53    inference(avatar_split_clause,[],[f806,f802,f748,f193])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    spl4_18 <=> v1_relat_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.53  fof(f748,plain,(
% 0.21/0.53    spl4_60 <=> r1_tarski(sK2,k1_relat_1(sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.21/0.53  fof(f802,plain,(
% 0.21/0.53    spl4_67 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.21/0.53  fof(f806,plain,(
% 0.21/0.53    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_67),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f805])).
% 0.21/0.53  fof(f805,plain,(
% 0.21/0.53    sK2 != sK2 | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_67),
% 0.21/0.53    inference(superposition,[],[f803,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.53  fof(f803,plain,(
% 0.21/0.53    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | spl4_67),
% 0.21/0.53    inference(avatar_component_clause,[],[f802])).
% 0.21/0.53  fof(f804,plain,(
% 0.21/0.53    ~spl4_52 | ~spl4_67 | spl4_66),
% 0.21/0.53    inference(avatar_split_clause,[],[f799,f792,f802,f706])).
% 0.21/0.53  fof(f706,plain,(
% 0.21/0.53    spl4_52 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.21/0.53  fof(f792,plain,(
% 0.21/0.53    spl4_66 <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.21/0.53  fof(f799,plain,(
% 0.21/0.53    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_66),
% 0.21/0.53    inference(superposition,[],[f793,f85])).
% 0.21/0.53  fof(f793,plain,(
% 0.21/0.53    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | spl4_66),
% 0.21/0.53    inference(avatar_component_clause,[],[f792])).
% 0.21/0.53  fof(f797,plain,(
% 0.21/0.53    ~spl4_52 | spl4_4 | ~spl4_66 | spl4_51),
% 0.21/0.53    inference(avatar_split_clause,[],[f741,f702,f792,f117,f706])).
% 0.21/0.53  fof(f702,plain,(
% 0.21/0.53    spl4_51 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.21/0.53  fof(f741,plain,(
% 0.21/0.53    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_51),
% 0.21/0.53    inference(resolution,[],[f703,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f57])).
% 0.21/0.53  fof(f703,plain,(
% 0.21/0.53    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_51),
% 0.21/0.53    inference(avatar_component_clause,[],[f702])).
% 0.21/0.53  fof(f789,plain,(
% 0.21/0.53    spl4_65 | ~spl4_53 | spl4_52),
% 0.21/0.53    inference(avatar_split_clause,[],[f766,f706,f710,f787])).
% 0.21/0.53  fof(f710,plain,(
% 0.21/0.53    spl4_53 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.21/0.53  fof(f766,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_52),
% 0.21/0.53    inference(resolution,[],[f707,f95])).
% 0.21/0.53  fof(f707,plain,(
% 0.21/0.53    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_52),
% 0.21/0.53    inference(avatar_component_clause,[],[f706])).
% 0.21/0.53  fof(f746,plain,(
% 0.21/0.53    ~spl4_18 | spl4_53),
% 0.21/0.53    inference(avatar_split_clause,[],[f742,f710,f193])).
% 0.21/0.53  fof(f742,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | spl4_53),
% 0.21/0.53    inference(resolution,[],[f711,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.53  fof(f711,plain,(
% 0.21/0.53    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_53),
% 0.21/0.53    inference(avatar_component_clause,[],[f710])).
% 0.21/0.53  fof(f736,plain,(
% 0.21/0.53    ~spl4_9 | ~spl4_7 | spl4_59 | ~spl4_7 | ~spl4_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f700,f136,f128,f734,f128,f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl4_9 <=> v1_funct_1(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.53  fof(f700,plain,(
% 0.21/0.53    ( ! [X11] : (m1_subset_1(k7_relat_1(sK3,X11),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) ) | (~spl4_7 | ~spl4_9)),
% 0.21/0.53    inference(superposition,[],[f98,f672])).
% 0.21/0.53  fof(f672,plain,(
% 0.21/0.53    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) ) | (~spl4_7 | ~spl4_9)),
% 0.21/0.53    inference(resolution,[],[f493,f129])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f128])).
% 0.21/0.53  fof(f493,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_9),
% 0.21/0.53    inference(resolution,[],[f96,f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    v1_funct_1(sK3) | ~spl4_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f136])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.53  fof(f708,plain,(
% 0.21/0.53    ~spl4_52 | spl4_3 | ~spl4_7 | ~spl4_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f689,f136,f128,f113,f706])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f689,plain,(
% 0.21/0.53    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_3 | ~spl4_7 | ~spl4_9)),
% 0.21/0.53    inference(superposition,[],[f114,f672])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f704,plain,(
% 0.21/0.53    ~spl4_51 | spl4_2 | ~spl4_7 | ~spl4_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f688,f136,f128,f110,f702])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f688,plain,(
% 0.21/0.53    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (spl4_2 | ~spl4_7 | ~spl4_9)),
% 0.21/0.53    inference(superposition,[],[f111,f672])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f110])).
% 0.21/0.53  fof(f492,plain,(
% 0.21/0.53    ~spl4_37 | ~spl4_7 | ~spl4_30),
% 0.21/0.53    inference(avatar_split_clause,[],[f483,f409,f128,f490])).
% 0.21/0.53  % (862)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f490,plain,(
% 0.21/0.53    spl4_37 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.53  fof(f409,plain,(
% 0.21/0.53    spl4_30 <=> ! [X1,X0] : (~r1_tarski(X0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.53  fof(f483,plain,(
% 0.21/0.53    ~r1_tarski(sK1,k1_xboole_0) | (~spl4_7 | ~spl4_30)),
% 0.21/0.53    inference(resolution,[],[f410,f129])).
% 0.21/0.53  fof(f410,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r1_tarski(X0,k1_xboole_0)) ) | ~spl4_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f409])).
% 0.21/0.53  fof(f429,plain,(
% 0.21/0.53    spl4_32 | ~spl4_22 | ~spl4_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f416,f376,f228,f426])).
% 0.21/0.53  fof(f426,plain,(
% 0.21/0.53    spl4_32 <=> k1_xboole_0 = sK3),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    spl4_27 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.53  fof(f416,plain,(
% 0.21/0.53    k1_xboole_0 = sK3 | (~spl4_22 | ~spl4_27)),
% 0.21/0.53    inference(resolution,[],[f377,f245])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f376])).
% 0.21/0.53  fof(f411,plain,(
% 0.21/0.53    ~spl4_18 | spl4_30 | spl4_26),
% 0.21/0.53    inference(avatar_split_clause,[],[f403,f373,f409,f193])).
% 0.21/0.53  fof(f373,plain,(
% 0.21/0.53    spl4_26 <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.53  fof(f403,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_relat_1(sK3)) ) | spl4_26),
% 0.21/0.53    inference(resolution,[],[f380,f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(resolution,[],[f87,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k2_relat_1(sK3),X1) | ~r1_tarski(X1,k1_xboole_0)) ) | spl4_26),
% 0.21/0.53    inference(resolution,[],[f374,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.53  fof(f374,plain,(
% 0.21/0.53    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | spl4_26),
% 0.21/0.53    inference(avatar_component_clause,[],[f373])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    ~spl4_26 | spl4_27 | ~spl4_25),
% 0.21/0.53    inference(avatar_split_clause,[],[f371,f367,f376,f373])).
% 0.21/0.53  fof(f367,plain,(
% 0.21/0.53    spl4_25 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~spl4_25),
% 0.21/0.53    inference(superposition,[],[f368,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f56])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~r1_tarski(k2_relat_1(sK3),X0)) ) | ~spl4_25),
% 0.21/0.53    inference(avatar_component_clause,[],[f367])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    ~spl4_18 | spl4_25 | ~spl4_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f363,f136,f367,f193])).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~v1_relat_1(sK3)) ) | ~spl4_9),
% 0.21/0.53    inference(resolution,[],[f77,f137])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  % (866)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    spl4_24 | ~spl4_7 | ~spl4_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f316,f228,f128,f322])).
% 0.21/0.53  fof(f316,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | (~spl4_7 | ~spl4_22)),
% 0.21/0.53    inference(resolution,[],[f297,f129])).
% 0.21/0.53  fof(f297,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0))) ) | ~spl4_22),
% 0.21/0.53    inference(resolution,[],[f260,f69])).
% 0.21/0.53  % (864)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~v1_relat_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k1_xboole_0 = k1_relat_1(k7_relat_1(X2,k1_xboole_0))) ) | ~spl4_22),
% 0.21/0.53    inference(resolution,[],[f251,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    ( ! [X8] : (~v1_relat_1(X8) | k1_xboole_0 = k1_relat_1(k7_relat_1(X8,k1_xboole_0))) ) | ~spl4_22),
% 0.21/0.53    inference(resolution,[],[f229,f70])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    ~spl4_7 | spl4_1 | ~spl4_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f239,f136,f107,f128])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_1 | ~spl4_9)),
% 0.21/0.53    inference(resolution,[],[f238,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f107])).
% 0.21/0.53  fof(f238,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_funct_1(k2_partfun1(X0,X1,sK3,X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_9),
% 0.21/0.53    inference(resolution,[],[f97,f137])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    ~spl4_15 | spl4_21 | ~spl4_11 | ~spl4_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f231,f164,f144,f222,f164])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    spl4_11 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_15)),
% 0.21/0.53    inference(forward_demodulation,[],[f218,f145])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f144])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~spl4_15),
% 0.21/0.53    inference(superposition,[],[f71,f212])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 0.21/0.53  fof(f230,plain,(
% 0.21/0.53    ~spl4_15 | spl4_22 | ~spl4_12 | ~spl4_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f226,f164,f148,f228,f164])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1 | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_12 | ~spl4_15)),
% 0.21/0.53    inference(forward_demodulation,[],[f225,f149])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_12 | ~spl4_15)),
% 0.21/0.53    inference(forward_demodulation,[],[f217,f149])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    ( ! [X1] : (k1_relat_1(k1_xboole_0) = X1 | ~r1_tarski(X1,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_15),
% 0.21/0.53    inference(superposition,[],[f72,f212])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    spl4_20),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    $false | spl4_20),
% 0.21/0.53    inference(resolution,[],[f204,f69])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f203])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    spl4_20 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    ~spl4_20 | ~spl4_7 | spl4_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f200,f193,f128,f203])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl4_7 | spl4_18)),
% 0.21/0.53    inference(resolution,[],[f199,f129])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_18),
% 0.21/0.53    inference(resolution,[],[f194,f68])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | spl4_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f193])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    spl4_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f162,f164])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    v1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(superposition,[],[f69,f99])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    spl4_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f65,f148])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    spl4_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f66,f144])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl4_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f58,f136])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  % (868)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f23])).
% 0.21/0.53  fof(f23,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    spl4_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f59,f132])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    spl4_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f60,f128])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl4_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f61,f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl4_6 <=> r1_tarski(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    r1_tarski(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ~spl4_4 | spl4_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f62,f120,f117])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    spl4_5 <=> k1_xboole_0 = sK0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f63,f113,f110,f107])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (858)------------------------------
% 0.21/0.53  % (858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (858)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (858)Memory used [KB]: 11513
% 0.21/0.53  % (858)Time elapsed: 0.057 s
% 0.21/0.53  % (858)------------------------------
% 0.21/0.53  % (858)------------------------------
% 0.21/0.53  % (851)Success in time 0.169 s
%------------------------------------------------------------------------------
