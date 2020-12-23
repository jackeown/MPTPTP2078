%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 534 expanded)
%              Number of leaves         :   59 ( 221 expanded)
%              Depth                    :   10
%              Number of atoms          :  815 (1783 expanded)
%              Number of equality atoms :  163 ( 457 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1029,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f136,f141,f146,f151,f158,f172,f181,f227,f264,f289,f296,f310,f315,f331,f339,f366,f378,f397,f402,f451,f467,f468,f477,f510,f535,f545,f549,f571,f593,f605,f608,f644,f689,f702,f812,f906,f942,f1006,f1025])).

fof(f1025,plain,
    ( spl4_60
    | ~ spl4_67 ),
    inference(avatar_contradiction_clause,[],[f1020])).

fof(f1020,plain,
    ( $false
    | spl4_60
    | ~ spl4_67 ),
    inference(unit_resulting_resolution,[],[f941,f77,f1005,f332])).

fof(f332,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f125,f121])).

fof(f121,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f125,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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

fof(f1005,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f1004,plain,
    ( spl4_67
  <=> ! [X1,X0] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f941,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_60 ),
    inference(avatar_component_clause,[],[f939])).

fof(f939,plain,
    ( spl4_60
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f1006,plain,
    ( spl4_67
    | ~ spl4_13
    | ~ spl4_41
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f954,f686,f590,f224,f1004])).

fof(f224,plain,
    ( spl4_13
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f590,plain,
    ( spl4_41
  <=> k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f686,plain,
    ( spl4_50
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f954,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_41
    | ~ spl4_50 ),
    inference(backward_demodulation,[],[f246,f926])).

fof(f926,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_41
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f918,f226])).

fof(f226,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f224])).

fof(f918,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl4_41
    | ~ spl4_50 ),
    inference(backward_demodulation,[],[f592,f688])).

fof(f688,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f686])).

fof(f592,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f590])).

fof(f246,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f109,f77])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f942,plain,
    ( ~ spl4_60
    | ~ spl4_13
    | spl4_38
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f937,f686,f563,f224,f939])).

fof(f563,plain,
    ( spl4_38
  <=> v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f937,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl4_13
    | spl4_38
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f936,f226])).

fof(f936,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_38
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f564,f688])).

fof(f564,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | spl4_38 ),
    inference(avatar_component_clause,[],[f563])).

fof(f906,plain,
    ( ~ spl4_34
    | ~ spl4_43
    | spl4_50
    | spl4_56 ),
    inference(avatar_contradiction_clause,[],[f904])).

fof(f904,plain,
    ( $false
    | ~ spl4_34
    | ~ spl4_43
    | spl4_50
    | spl4_56 ),
    inference(unit_resulting_resolution,[],[f687,f811,f476,f636,f321])).

fof(f321,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f124,f120])).

fof(f120,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f124,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f636,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f634])).

fof(f634,plain,
    ( spl4_43
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f476,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl4_34
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f811,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_56 ),
    inference(avatar_component_clause,[],[f809])).

fof(f809,plain,
    ( spl4_56
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f687,plain,
    ( k1_xboole_0 != sK2
    | spl4_50 ),
    inference(avatar_component_clause,[],[f686])).

fof(f812,plain,
    ( ~ spl4_56
    | spl4_36
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f789,f699,f519,f809])).

fof(f519,plain,
    ( spl4_36
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f699,plain,
    ( spl4_51
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f789,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_36
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f520,f701])).

fof(f701,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f699])).

fof(f520,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f519])).

fof(f702,plain,
    ( spl4_51
    | ~ spl4_33
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f690,f683,f464,f699])).

fof(f464,plain,
    ( spl4_33
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f683,plain,
    ( spl4_49
  <=> ! [X1] :
        ( ~ v1_funct_2(sK2,X1,k1_xboole_0)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f690,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_33
    | ~ spl4_49 ),
    inference(resolution,[],[f684,f466])).

fof(f466,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f464])).

fof(f684,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f683])).

fof(f689,plain,
    ( spl4_49
    | spl4_50
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f561,f474,f686,f683])).

fof(f561,plain,
    ( ! [X1] :
        ( k1_xboole_0 = sK2
        | ~ v1_funct_2(sK2,X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl4_34 ),
    inference(resolution,[],[f476,f321])).

fof(f644,plain,
    ( spl4_43
    | ~ spl4_22
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f620,f444,f336,f634])).

fof(f336,plain,
    ( spl4_22
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f444,plain,
    ( spl4_31
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f620,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl4_22
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f338,f446])).

fof(f446,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f444])).

fof(f338,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f336])).

fof(f608,plain,
    ( k1_xboole_0 != sK1
    | k2_funct_1(sK2) != k4_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f605,plain,
    ( ~ spl4_19
    | ~ spl4_21
    | spl4_39
    | ~ spl4_41 ),
    inference(avatar_contradiction_clause,[],[f604])).

fof(f604,plain,
    ( $false
    | ~ spl4_19
    | ~ spl4_21
    | spl4_39
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f603,f570])).

fof(f570,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl4_39
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f603,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f602,f121])).

fof(f602,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(sK2)))))
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f601,f330])).

fof(f330,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl4_21
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f601,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(sK2)))))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_19
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f599,f314])).

fof(f314,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl4_19
  <=> v1_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f599,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(sK2)))))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_41 ),
    inference(superposition,[],[f90,f592])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f593,plain,
    ( spl4_41
    | ~ spl4_23
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f555,f444,f363,f590])).

fof(f363,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f555,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_23
    | ~ spl4_31 ),
    inference(backward_demodulation,[],[f365,f446])).

fof(f365,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f363])).

fof(f571,plain,
    ( ~ spl4_39
    | ~ spl4_31
    | spl4_35 ),
    inference(avatar_split_clause,[],[f558,f507,f444,f568])).

fof(f507,plain,
    ( spl4_35
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f558,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_31
    | spl4_35 ),
    inference(forward_demodulation,[],[f556,f121])).

fof(f556,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_31
    | spl4_35 ),
    inference(backward_demodulation,[],[f509,f446])).

fof(f509,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f507])).

fof(f549,plain,
    ( sK0 != k1_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f545,plain,
    ( ~ spl4_19
    | ~ spl4_21
    | ~ spl4_23
    | spl4_35
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_23
    | spl4_35
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f543,f509])).

fof(f543,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_23
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f542,f365])).

fof(f542,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),sK0)))
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f541,f330])).

fof(f541,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),sK0)))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_19
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f537,f314])).

fof(f537,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_37 ),
    inference(superposition,[],[f90,f534])).

fof(f534,plain,
    ( sK0 = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f532])).

fof(f532,plain,
    ( spl4_37
  <=> sK0 = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f535,plain,
    ( spl4_37
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f517,f448,f394,f375,f532])).

fof(f375,plain,
    ( spl4_24
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f394,plain,
    ( spl4_25
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f448,plain,
    ( spl4_32
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f517,plain,
    ( sK0 = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f377,f514])).

fof(f514,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_25
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f396,f450])).

fof(f450,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f448])).

fof(f396,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f394])).

fof(f377,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f375])).

fof(f510,plain,
    ( ~ spl4_35
    | spl4_17
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f478,f307,f286,f507])).

fof(f286,plain,
    ( spl4_17
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f307,plain,
    ( spl4_18
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f478,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_17
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f288,f309])).

fof(f309,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f307])).

fof(f288,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f286])).

fof(f477,plain,
    ( spl4_34
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f462,f444,f143,f474])).

fof(f143,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f462,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f453,f120])).

fof(f453,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(backward_demodulation,[],[f145,f446])).

fof(f145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f468,plain,
    ( k2_funct_1(sK2) != k4_relat_1(sK2)
    | sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f467,plain,
    ( spl4_33
    | ~ spl4_3
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f452,f444,f138,f464])).

fof(f138,plain,
    ( spl4_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f452,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_31 ),
    inference(backward_demodulation,[],[f140,f446])).

fof(f140,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f138])).

fof(f451,plain,
    ( spl4_31
    | spl4_32
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f358,f143,f138,f448,f444])).

fof(f358,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f354,f145])).

fof(f354,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(resolution,[],[f111,f140])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f402,plain,
    ( spl4_26
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f389,f375,f363,f328,f312,f399])).

fof(f399,plain,
    ( spl4_26
  <=> v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f389,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f388,f365])).

fof(f388,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f387,f330])).

fof(f387,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_19
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f381,f314])).

fof(f381,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_24 ),
    inference(superposition,[],[f89,f377])).

fof(f89,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f397,plain,
    ( spl4_25
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f247,f143,f394])).

fof(f247,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f109,f145])).

fof(f378,plain,
    ( spl4_24
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f373,f307,f178,f133,f128,f375])).

fof(f128,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f133,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f178,plain,
    ( spl4_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f373,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f240,f309])).

fof(f240,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f239,f180])).

fof(f180,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f178])).

fof(f239,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f237,f130])).

fof(f130,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f128])).

fof(f237,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f95,f135])).

fof(f135,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f133])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f366,plain,
    ( spl4_23
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f361,f307,f261,f178,f133,f128,f363])).

fof(f261,plain,
    ( spl4_14
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f361,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f360,f263])).

fof(f263,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f261])).

fof(f360,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f233,f309])).

fof(f233,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f232,f180])).

fof(f232,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f230,f130])).

fof(f230,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f94,f135])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f339,plain,
    ( spl4_22
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f271,f261,f178,f128,f336])).

fof(f271,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f270,f180])).

fof(f270,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f267,f130])).

fof(f267,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(superposition,[],[f89,f263])).

fof(f331,plain,
    ( spl4_21
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f325,f307,f178,f128,f328])).

fof(f325,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f324,f180])).

fof(f324,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f323,f130])).

fof(f323,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f91,f309])).

fof(f91,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f315,plain,
    ( spl4_19
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f305,f278,f178,f133,f128,f312])).

fof(f278,plain,
    ( spl4_15
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f305,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f279,f212])).

fof(f212,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f211,f180])).

fof(f211,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f209,f130])).

fof(f209,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f93,f135])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f279,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f278])).

fof(f310,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f212,f178,f133,f128,f307])).

fof(f296,plain,
    ( ~ spl4_1
    | ~ spl4_9
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_9
    | spl4_15 ),
    inference(subsumption_resolution,[],[f294,f180])).

fof(f294,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_1
    | spl4_15 ),
    inference(subsumption_resolution,[],[f291,f130])).

fof(f291,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_15 ),
    inference(resolution,[],[f280,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f280,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f278])).

fof(f289,plain,
    ( ~ spl4_15
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f75,f286,f282,f278])).

fof(f282,plain,
    ( spl4_16
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f75,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f59])).

fof(f59,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
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

fof(f264,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f259,f148,f143,f261])).

fof(f148,plain,
    ( spl4_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f259,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f255,f150])).

fof(f150,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f255,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f110,f145])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f227,plain,
    ( spl4_13
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f203,f169,f224])).

fof(f169,plain,
    ( spl4_8
  <=> v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f203,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl4_8 ),
    inference(resolution,[],[f171,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f171,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f181,plain,
    ( spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f174,f143,f178])).

fof(f174,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f108,f145])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f172,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f160,f155,f169])).

fof(f155,plain,
    ( spl4_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f160,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl4_6 ),
    inference(resolution,[],[f157,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f157,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f155])).

fof(f158,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f153,f155])).

fof(f153,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f152,f76])).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f152,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f107,f98])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f62,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f151,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f74,f148])).

fof(f74,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f146,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f72,f143])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f60])).

fof(f141,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f71,f138])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f136,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f73,f133])).

fof(f73,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f131,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f70,f128])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (22719)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (22724)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (22721)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (22727)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (22718)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (22740)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (22723)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (22734)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (22722)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (22737)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (22742)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (22726)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (22732)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (22735)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (22733)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (22718)Refutation not found, incomplete strategy% (22718)------------------------------
% 0.21/0.51  % (22718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22729)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (22741)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (22723)Refutation not found, incomplete strategy% (22723)------------------------------
% 0.21/0.52  % (22723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22739)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (22736)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (22723)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22723)Memory used [KB]: 10746
% 0.21/0.52  % (22723)Time elapsed: 0.078 s
% 0.21/0.52  % (22723)------------------------------
% 0.21/0.52  % (22723)------------------------------
% 0.21/0.52  % (22717)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (22730)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (22720)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (22731)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (22738)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (22718)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22718)Memory used [KB]: 10746
% 0.21/0.53  % (22718)Time elapsed: 0.105 s
% 0.21/0.53  % (22718)------------------------------
% 0.21/0.53  % (22718)------------------------------
% 0.21/0.53  % (22725)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (22719)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1029,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f131,f136,f141,f146,f151,f158,f172,f181,f227,f264,f289,f296,f310,f315,f331,f339,f366,f378,f397,f402,f451,f467,f468,f477,f510,f535,f545,f549,f571,f593,f605,f608,f644,f689,f702,f812,f906,f942,f1006,f1025])).
% 0.21/0.53  fof(f1025,plain,(
% 0.21/0.53    spl4_60 | ~spl4_67),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1020])).
% 0.21/0.53  fof(f1020,plain,(
% 0.21/0.53    $false | (spl4_60 | ~spl4_67)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f941,f77,f1005,f332])).
% 0.21/0.53  fof(f332,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f125,f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(flattening,[],[f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f114])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  fof(f1005,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl4_67),
% 0.21/0.54    inference(avatar_component_clause,[],[f1004])).
% 0.21/0.54  fof(f1004,plain,(
% 0.21/0.54    spl4_67 <=> ! [X1,X0] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.54  fof(f941,plain,(
% 0.21/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl4_60),
% 0.21/0.54    inference(avatar_component_clause,[],[f939])).
% 0.21/0.54  fof(f939,plain,(
% 0.21/0.54    spl4_60 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.21/0.54  fof(f1006,plain,(
% 0.21/0.54    spl4_67 | ~spl4_13 | ~spl4_41 | ~spl4_50),
% 0.21/0.54    inference(avatar_split_clause,[],[f954,f686,f590,f224,f1004])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    spl4_13 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.54  fof(f590,plain,(
% 0.21/0.54    spl4_41 <=> k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.54  fof(f686,plain,(
% 0.21/0.54    spl4_50 <=> k1_xboole_0 = sK2),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.21/0.54  fof(f954,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl4_13 | ~spl4_41 | ~spl4_50)),
% 0.21/0.54    inference(backward_demodulation,[],[f246,f926])).
% 0.21/0.54  fof(f926,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_13 | ~spl4_41 | ~spl4_50)),
% 0.21/0.54    inference(forward_demodulation,[],[f918,f226])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl4_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f224])).
% 0.21/0.54  fof(f918,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0)) | (~spl4_41 | ~spl4_50)),
% 0.21/0.54    inference(backward_demodulation,[],[f592,f688])).
% 0.21/0.54  fof(f688,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~spl4_50),
% 0.21/0.54    inference(avatar_component_clause,[],[f686])).
% 0.21/0.54  fof(f592,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) | ~spl4_41),
% 0.21/0.54    inference(avatar_component_clause,[],[f590])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f109,f77])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f942,plain,(
% 0.21/0.54    ~spl4_60 | ~spl4_13 | spl4_38 | ~spl4_50),
% 0.21/0.54    inference(avatar_split_clause,[],[f937,f686,f563,f224,f939])).
% 0.21/0.54  fof(f563,plain,(
% 0.21/0.54    spl4_38 <=> v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.54  fof(f937,plain,(
% 0.21/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (~spl4_13 | spl4_38 | ~spl4_50)),
% 0.21/0.54    inference(forward_demodulation,[],[f936,f226])).
% 0.21/0.54  fof(f936,plain,(
% 0.21/0.54    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_38 | ~spl4_50)),
% 0.21/0.54    inference(forward_demodulation,[],[f564,f688])).
% 0.21/0.54  fof(f564,plain,(
% 0.21/0.54    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | spl4_38),
% 0.21/0.54    inference(avatar_component_clause,[],[f563])).
% 0.21/0.54  fof(f906,plain,(
% 0.21/0.54    ~spl4_34 | ~spl4_43 | spl4_50 | spl4_56),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f904])).
% 0.21/0.54  fof(f904,plain,(
% 0.21/0.54    $false | (~spl4_34 | ~spl4_43 | spl4_50 | spl4_56)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f687,f811,f476,f636,f321])).
% 0.21/0.54  fof(f321,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(forward_demodulation,[],[f124,f120])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f106])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f68])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f69])).
% 0.21/0.54  fof(f636,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~spl4_43),
% 0.21/0.54    inference(avatar_component_clause,[],[f634])).
% 0.21/0.54  fof(f634,plain,(
% 0.21/0.54    spl4_43 <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.54  fof(f476,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_34),
% 0.21/0.54    inference(avatar_component_clause,[],[f474])).
% 0.21/0.54  fof(f474,plain,(
% 0.21/0.54    spl4_34 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.54  fof(f811,plain,(
% 0.21/0.54    k1_xboole_0 != k1_relat_1(sK2) | spl4_56),
% 0.21/0.54    inference(avatar_component_clause,[],[f809])).
% 0.21/0.54  fof(f809,plain,(
% 0.21/0.54    spl4_56 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.21/0.54  fof(f687,plain,(
% 0.21/0.54    k1_xboole_0 != sK2 | spl4_50),
% 0.21/0.54    inference(avatar_component_clause,[],[f686])).
% 0.21/0.54  fof(f812,plain,(
% 0.21/0.54    ~spl4_56 | spl4_36 | ~spl4_51),
% 0.21/0.54    inference(avatar_split_clause,[],[f789,f699,f519,f809])).
% 0.21/0.54  fof(f519,plain,(
% 0.21/0.54    spl4_36 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.54  fof(f699,plain,(
% 0.21/0.54    spl4_51 <=> k1_xboole_0 = sK0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.21/0.54  fof(f789,plain,(
% 0.21/0.54    k1_xboole_0 != k1_relat_1(sK2) | (spl4_36 | ~spl4_51)),
% 0.21/0.54    inference(forward_demodulation,[],[f520,f701])).
% 0.21/0.54  fof(f701,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | ~spl4_51),
% 0.21/0.54    inference(avatar_component_clause,[],[f699])).
% 0.21/0.54  fof(f520,plain,(
% 0.21/0.54    sK0 != k1_relat_1(sK2) | spl4_36),
% 0.21/0.54    inference(avatar_component_clause,[],[f519])).
% 0.21/0.54  fof(f702,plain,(
% 0.21/0.54    spl4_51 | ~spl4_33 | ~spl4_49),
% 0.21/0.54    inference(avatar_split_clause,[],[f690,f683,f464,f699])).
% 0.21/0.54  fof(f464,plain,(
% 0.21/0.54    spl4_33 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.54  fof(f683,plain,(
% 0.21/0.54    spl4_49 <=> ! [X1] : (~v1_funct_2(sK2,X1,k1_xboole_0) | k1_xboole_0 = X1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.54  fof(f690,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | (~spl4_33 | ~spl4_49)),
% 0.21/0.54    inference(resolution,[],[f684,f466])).
% 0.21/0.54  fof(f466,plain,(
% 0.21/0.54    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl4_33),
% 0.21/0.54    inference(avatar_component_clause,[],[f464])).
% 0.21/0.54  fof(f684,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_funct_2(sK2,X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl4_49),
% 0.21/0.54    inference(avatar_component_clause,[],[f683])).
% 0.21/0.54  fof(f689,plain,(
% 0.21/0.54    spl4_49 | spl4_50 | ~spl4_34),
% 0.21/0.54    inference(avatar_split_clause,[],[f561,f474,f686,f683])).
% 0.21/0.54  fof(f561,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = sK2 | ~v1_funct_2(sK2,X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl4_34),
% 0.21/0.54    inference(resolution,[],[f476,f321])).
% 0.21/0.54  fof(f644,plain,(
% 0.21/0.54    spl4_43 | ~spl4_22 | ~spl4_31),
% 0.21/0.54    inference(avatar_split_clause,[],[f620,f444,f336,f634])).
% 0.21/0.54  fof(f336,plain,(
% 0.21/0.54    spl4_22 <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.54  fof(f444,plain,(
% 0.21/0.54    spl4_31 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.54  fof(f620,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (~spl4_22 | ~spl4_31)),
% 0.21/0.54    inference(forward_demodulation,[],[f338,f446])).
% 0.21/0.54  fof(f446,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl4_31),
% 0.21/0.54    inference(avatar_component_clause,[],[f444])).
% 0.21/0.54  fof(f338,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~spl4_22),
% 0.21/0.54    inference(avatar_component_clause,[],[f336])).
% 0.21/0.54  fof(f608,plain,(
% 0.21/0.54    k1_xboole_0 != sK1 | k2_funct_1(sK2) != k4_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f605,plain,(
% 0.21/0.54    ~spl4_19 | ~spl4_21 | spl4_39 | ~spl4_41),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f604])).
% 0.21/0.54  fof(f604,plain,(
% 0.21/0.54    $false | (~spl4_19 | ~spl4_21 | spl4_39 | ~spl4_41)),
% 0.21/0.54    inference(subsumption_resolution,[],[f603,f570])).
% 0.21/0.54  fof(f570,plain,(
% 0.21/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | spl4_39),
% 0.21/0.54    inference(avatar_component_clause,[],[f568])).
% 0.21/0.54  fof(f568,plain,(
% 0.21/0.54    spl4_39 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.54  fof(f603,plain,(
% 0.21/0.54    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl4_19 | ~spl4_21 | ~spl4_41)),
% 0.21/0.54    inference(forward_demodulation,[],[f602,f121])).
% 0.21/0.54  fof(f602,plain,(
% 0.21/0.54    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(sK2))))) | (~spl4_19 | ~spl4_21 | ~spl4_41)),
% 0.21/0.54    inference(subsumption_resolution,[],[f601,f330])).
% 0.21/0.54  fof(f330,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(sK2)) | ~spl4_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f328])).
% 0.21/0.54  fof(f328,plain,(
% 0.21/0.54    spl4_21 <=> v1_relat_1(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.54  fof(f601,plain,(
% 0.21/0.54    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(sK2))))) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_19 | ~spl4_41)),
% 0.21/0.54    inference(subsumption_resolution,[],[f599,f314])).
% 0.21/0.54  fof(f314,plain,(
% 0.21/0.54    v1_funct_1(k4_relat_1(sK2)) | ~spl4_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f312])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    spl4_19 <=> v1_funct_1(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.54  fof(f599,plain,(
% 0.21/0.54    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(sK2))))) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_41),
% 0.21/0.54    inference(superposition,[],[f90,f592])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.54  fof(f593,plain,(
% 0.21/0.54    spl4_41 | ~spl4_23 | ~spl4_31),
% 0.21/0.54    inference(avatar_split_clause,[],[f555,f444,f363,f590])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    spl4_23 <=> sK1 = k1_relat_1(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.54  fof(f555,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) | (~spl4_23 | ~spl4_31)),
% 0.21/0.54    inference(backward_demodulation,[],[f365,f446])).
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    sK1 = k1_relat_1(k4_relat_1(sK2)) | ~spl4_23),
% 0.21/0.54    inference(avatar_component_clause,[],[f363])).
% 0.21/0.54  fof(f571,plain,(
% 0.21/0.54    ~spl4_39 | ~spl4_31 | spl4_35),
% 0.21/0.54    inference(avatar_split_clause,[],[f558,f507,f444,f568])).
% 0.21/0.54  fof(f507,plain,(
% 0.21/0.54    spl4_35 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.54  fof(f558,plain,(
% 0.21/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl4_31 | spl4_35)),
% 0.21/0.54    inference(forward_demodulation,[],[f556,f121])).
% 0.21/0.54  fof(f556,plain,(
% 0.21/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl4_31 | spl4_35)),
% 0.21/0.54    inference(backward_demodulation,[],[f509,f446])).
% 0.21/0.54  fof(f509,plain,(
% 0.21/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_35),
% 0.21/0.54    inference(avatar_component_clause,[],[f507])).
% 0.21/0.54  fof(f549,plain,(
% 0.21/0.54    sK0 != k1_relat_1(sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f545,plain,(
% 0.21/0.54    ~spl4_19 | ~spl4_21 | ~spl4_23 | spl4_35 | ~spl4_37),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f544])).
% 0.21/0.54  fof(f544,plain,(
% 0.21/0.54    $false | (~spl4_19 | ~spl4_21 | ~spl4_23 | spl4_35 | ~spl4_37)),
% 0.21/0.54    inference(subsumption_resolution,[],[f543,f509])).
% 0.21/0.54  fof(f543,plain,(
% 0.21/0.54    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_19 | ~spl4_21 | ~spl4_23 | ~spl4_37)),
% 0.21/0.54    inference(forward_demodulation,[],[f542,f365])).
% 0.21/0.54  fof(f542,plain,(
% 0.21/0.54    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),sK0))) | (~spl4_19 | ~spl4_21 | ~spl4_37)),
% 0.21/0.54    inference(subsumption_resolution,[],[f541,f330])).
% 0.21/0.54  fof(f541,plain,(
% 0.21/0.54    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),sK0))) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_19 | ~spl4_37)),
% 0.21/0.54    inference(subsumption_resolution,[],[f537,f314])).
% 0.21/0.54  fof(f537,plain,(
% 0.21/0.54    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_37),
% 0.21/0.54    inference(superposition,[],[f90,f534])).
% 0.21/0.54  fof(f534,plain,(
% 0.21/0.54    sK0 = k2_relat_1(k4_relat_1(sK2)) | ~spl4_37),
% 0.21/0.54    inference(avatar_component_clause,[],[f532])).
% 0.21/0.54  fof(f532,plain,(
% 0.21/0.54    spl4_37 <=> sK0 = k2_relat_1(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.54  fof(f535,plain,(
% 0.21/0.54    spl4_37 | ~spl4_24 | ~spl4_25 | ~spl4_32),
% 0.21/0.54    inference(avatar_split_clause,[],[f517,f448,f394,f375,f532])).
% 0.21/0.54  fof(f375,plain,(
% 0.21/0.54    spl4_24 <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.54  fof(f394,plain,(
% 0.21/0.54    spl4_25 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.54  fof(f448,plain,(
% 0.21/0.54    spl4_32 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.54  fof(f517,plain,(
% 0.21/0.54    sK0 = k2_relat_1(k4_relat_1(sK2)) | (~spl4_24 | ~spl4_25 | ~spl4_32)),
% 0.21/0.54    inference(backward_demodulation,[],[f377,f514])).
% 0.21/0.54  fof(f514,plain,(
% 0.21/0.54    sK0 = k1_relat_1(sK2) | (~spl4_25 | ~spl4_32)),
% 0.21/0.54    inference(forward_demodulation,[],[f396,f450])).
% 0.21/0.54  fof(f450,plain,(
% 0.21/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_32),
% 0.21/0.54    inference(avatar_component_clause,[],[f448])).
% 0.21/0.54  fof(f396,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl4_25),
% 0.21/0.54    inference(avatar_component_clause,[],[f394])).
% 0.21/0.54  fof(f377,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~spl4_24),
% 0.21/0.54    inference(avatar_component_clause,[],[f375])).
% 0.21/0.54  fof(f510,plain,(
% 0.21/0.54    ~spl4_35 | spl4_17 | ~spl4_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f478,f307,f286,f507])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    spl4_17 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    spl4_18 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.54  fof(f478,plain,(
% 0.21/0.54    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl4_17 | ~spl4_18)),
% 0.21/0.54    inference(forward_demodulation,[],[f288,f309])).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl4_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f307])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f286])).
% 0.21/0.54  fof(f477,plain,(
% 0.21/0.54    spl4_34 | ~spl4_4 | ~spl4_31),
% 0.21/0.54    inference(avatar_split_clause,[],[f462,f444,f143,f474])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f462,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_4 | ~spl4_31)),
% 0.21/0.54    inference(forward_demodulation,[],[f453,f120])).
% 0.21/0.54  fof(f453,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl4_4 | ~spl4_31)),
% 0.21/0.54    inference(backward_demodulation,[],[f145,f446])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f143])).
% 0.21/0.54  fof(f468,plain,(
% 0.21/0.54    k2_funct_1(sK2) != k4_relat_1(sK2) | sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f467,plain,(
% 0.21/0.54    spl4_33 | ~spl4_3 | ~spl4_31),
% 0.21/0.54    inference(avatar_split_clause,[],[f452,f444,f138,f464])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    spl4_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f452,plain,(
% 0.21/0.54    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl4_3 | ~spl4_31)),
% 0.21/0.54    inference(backward_demodulation,[],[f140,f446])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    v1_funct_2(sK2,sK0,sK1) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f138])).
% 0.21/0.54  fof(f451,plain,(
% 0.21/0.54    spl4_31 | spl4_32 | ~spl4_3 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f358,f143,f138,f448,f444])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | (~spl4_3 | ~spl4_4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f354,f145])).
% 0.21/0.54  fof(f354,plain,(
% 0.21/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f111,f140])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f69])).
% 0.21/0.54  fof(f402,plain,(
% 0.21/0.54    spl4_26 | ~spl4_19 | ~spl4_21 | ~spl4_23 | ~spl4_24),
% 0.21/0.54    inference(avatar_split_clause,[],[f389,f375,f363,f328,f312,f399])).
% 0.21/0.54  fof(f399,plain,(
% 0.21/0.54    spl4_26 <=> v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.54  fof(f389,plain,(
% 0.21/0.54    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) | (~spl4_19 | ~spl4_21 | ~spl4_23 | ~spl4_24)),
% 0.21/0.54    inference(forward_demodulation,[],[f388,f365])).
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | (~spl4_19 | ~spl4_21 | ~spl4_24)),
% 0.21/0.54    inference(subsumption_resolution,[],[f387,f330])).
% 0.21/0.54  fof(f387,plain,(
% 0.21/0.54    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_19 | ~spl4_24)),
% 0.21/0.54    inference(subsumption_resolution,[],[f381,f314])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_24),
% 0.21/0.54    inference(superposition,[],[f89,f377])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f397,plain,(
% 0.21/0.54    spl4_25 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f247,f143,f394])).
% 0.21/0.54  fof(f247,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl4_4),
% 0.21/0.54    inference(resolution,[],[f109,f145])).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    spl4_24 | ~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f373,f307,f178,f133,f128,f375])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl4_1 <=> v1_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    spl4_2 <=> v2_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    spl4_9 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.54  fof(f373,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_18)),
% 0.21/0.54    inference(forward_demodulation,[],[f240,f309])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f239,f180])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl4_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f178])).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f237,f130])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    v1_funct_1(sK2) | ~spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f128])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f95,f135])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    v2_funct_1(sK2) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f133])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    spl4_23 | ~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_14 | ~spl4_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f361,f307,f261,f178,f133,f128,f363])).
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    spl4_14 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    sK1 = k1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_14 | ~spl4_18)),
% 0.21/0.54    inference(forward_demodulation,[],[f360,f263])).
% 0.21/0.54  fof(f263,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2) | ~spl4_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f261])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_18)),
% 0.21/0.54    inference(forward_demodulation,[],[f233,f309])).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f232,f180])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f230,f130])).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f94,f135])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    spl4_22 | ~spl4_1 | ~spl4_9 | ~spl4_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f271,f261,f178,f128,f336])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | (~spl4_1 | ~spl4_9 | ~spl4_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f270,f180])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f267,f130])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_14),
% 0.21/0.54    inference(superposition,[],[f89,f263])).
% 0.21/0.54  fof(f331,plain,(
% 0.21/0.54    spl4_21 | ~spl4_1 | ~spl4_9 | ~spl4_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f325,f307,f178,f128,f328])).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_9 | ~spl4_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f324,f180])).
% 0.21/0.54  fof(f324,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_18)),
% 0.21/0.54    inference(subsumption_resolution,[],[f323,f130])).
% 0.21/0.54  fof(f323,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_18),
% 0.21/0.54    inference(superposition,[],[f91,f309])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.54  fof(f315,plain,(
% 0.21/0.54    spl4_19 | ~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f305,f278,f178,f133,f128,f312])).
% 0.21/0.54  fof(f278,plain,(
% 0.21/0.54    spl4_15 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    v1_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_15)),
% 0.21/0.54    inference(backward_demodulation,[],[f279,f212])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f211,f180])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f209,f130])).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 0.21/0.54    inference(resolution,[],[f93,f135])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.54  fof(f279,plain,(
% 0.21/0.54    v1_funct_1(k2_funct_1(sK2)) | ~spl4_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f278])).
% 0.21/0.54  fof(f310,plain,(
% 0.21/0.54    spl4_18 | ~spl4_1 | ~spl4_2 | ~spl4_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f212,f178,f133,f128,f307])).
% 0.21/0.54  fof(f296,plain,(
% 0.21/0.54    ~spl4_1 | ~spl4_9 | spl4_15),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f295])).
% 0.21/0.54  fof(f295,plain,(
% 0.21/0.54    $false | (~spl4_1 | ~spl4_9 | spl4_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f294,f180])).
% 0.21/0.54  fof(f294,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | (~spl4_1 | spl4_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f291,f130])).
% 0.21/0.54  fof(f291,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_15),
% 0.21/0.54    inference(resolution,[],[f280,f92])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(sK2)) | spl4_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f278])).
% 0.21/0.54  fof(f289,plain,(
% 0.21/0.54    ~spl4_15 | ~spl4_16 | ~spl4_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f75,f286,f282,f278])).
% 0.21/0.54  fof(f282,plain,(
% 0.21/0.54    spl4_16 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f26])).
% 0.21/0.54  fof(f26,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    spl4_14 | ~spl4_4 | ~spl4_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f259,f148,f143,f261])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    spl4_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2) | (~spl4_4 | ~spl4_5)),
% 0.21/0.54    inference(forward_demodulation,[],[f255,f150])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f148])).
% 0.21/0.54  fof(f255,plain,(
% 0.21/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl4_4),
% 0.21/0.54    inference(resolution,[],[f110,f145])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    spl4_13 | ~spl4_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f203,f169,f224])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    spl4_8 <=> v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl4_8),
% 0.21/0.54    inference(resolution,[],[f171,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl4_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f169])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    spl4_9 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f174,f143,f178])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl4_4),
% 0.21/0.54    inference(resolution,[],[f108,f145])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    spl4_8 | ~spl4_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f160,f155,f169])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    spl4_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl4_6),
% 0.21/0.54    inference(resolution,[],[f157,f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k4_relat_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0) | ~spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f155])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    spl4_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f153,f155])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f152,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,sK3(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(resolution,[],[f107,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f62,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.54    inference(rectify,[],[f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    spl4_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f74,f148])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f60])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f72,f143])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f60])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f71,f138])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f60])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f73,f133])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    v2_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f60])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f70,f128])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f60])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (22719)------------------------------
% 0.21/0.54  % (22719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22719)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (22719)Memory used [KB]: 6652
% 0.21/0.54  % (22719)Time elapsed: 0.128 s
% 0.21/0.54  % (22719)------------------------------
% 0.21/0.54  % (22719)------------------------------
% 0.21/0.54  % (22716)Success in time 0.183 s
%------------------------------------------------------------------------------
