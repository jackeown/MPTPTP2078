%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 300 expanded)
%              Number of leaves         :   47 ( 128 expanded)
%              Depth                    :   10
%              Number of atoms          :  550 (1073 expanded)
%              Number of equality atoms :  128 ( 232 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f459,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f102,f106,f110,f114,f118,f122,f140,f145,f147,f153,f193,f203,f207,f214,f219,f222,f249,f270,f282,f349,f351,f355,f368,f375,f376,f383,f454])).

fof(f454,plain,
    ( ~ spl4_9
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | ~ spl4_9
    | spl4_41 ),
    inference(resolution,[],[f382,f181])).

fof(f181,plain,
    ( ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2)
    | ~ spl4_9 ),
    inference(superposition,[],[f72,f157])).

fof(f157,plain,
    ( ! [X1] : k1_xboole_0 = sK3(k1_xboole_0,X1)
    | ~ spl4_9 ),
    inference(resolution,[],[f154,f150])).

fof(f150,plain,(
    ! [X1] : m1_subset_1(sK3(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f69,f83])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X1] : m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK3(X0,X1),X0,X1)
      & v1_funct_1(sK3(X0,X1))
      & v1_relat_1(sK3(X0,X1))
      & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK3(X0,X1),X0,X1)
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_9 ),
    inference(resolution,[],[f148,f121])).

fof(f121,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f72,plain,(
    ! [X0,X1] : v1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f44])).

fof(f382,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl4_41
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f383,plain,
    ( ~ spl4_41
    | spl4_2
    | ~ spl4_30
    | ~ spl4_33
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f379,f358,f280,f268,f93,f381])).

fof(f93,plain,
    ( spl4_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f268,plain,
    ( spl4_30
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f280,plain,
    ( spl4_33
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f358,plain,
    ( spl4_37
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f379,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_30
    | ~ spl4_33
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f378,f359])).

fof(f359,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f358])).

fof(f378,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_30
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f377,f281])).

fof(f281,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f280])).

fof(f377,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl4_2
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f94,f347])).

fof(f347,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f268])).

fof(f94,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f376,plain,
    ( k1_xboole_0 != k2_funct_1(sK2)
    | k1_xboole_0 != sK2
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f375,plain,
    ( ~ spl4_40
    | spl4_3
    | ~ spl4_30
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f371,f280,f268,f96,f373])).

fof(f373,plain,
    ( spl4_40
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f96,plain,
    ( spl4_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f371,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_30
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f370,f281])).

fof(f370,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f369,f83])).

fof(f369,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_3
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f97,f347])).

fof(f97,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f368,plain,
    ( spl4_37
    | ~ spl4_20
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f367,f280,f209,f358])).

fof(f209,plain,
    ( spl4_20
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f367,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl4_20
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f210,f281])).

fof(f210,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f355,plain,
    ( sK1 != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f351,plain,
    ( sK1 != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f349,plain,
    ( spl4_36
    | spl4_30
    | ~ spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f339,f108,f112,f268,f345])).

fof(f345,plain,
    ( spl4_36
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f112,plain,
    ( spl4_7
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f108,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f339,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f310,f109])).

fof(f109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f310,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | k1_relat_1(X5) = X3 ) ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f76,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f282,plain,
    ( ~ spl4_12
    | spl4_33
    | ~ spl4_30
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f258,f246,f268,f280,f137])).

fof(f137,plain,
    ( spl4_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f246,plain,
    ( spl4_26
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f258,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl4_26 ),
    inference(superposition,[],[f57,f247])).

fof(f247,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f246])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

% (8749)Refutation not found, incomplete strategy% (8749)------------------------------
% (8749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f270,plain,
    ( ~ spl4_30
    | spl4_21
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f255,f246,f212,f268])).

fof(f212,plain,
    ( spl4_21
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f255,plain,
    ( k1_xboole_0 != sK1
    | spl4_21
    | ~ spl4_26 ),
    inference(superposition,[],[f213,f247])).

fof(f213,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f212])).

fof(f249,plain,
    ( ~ spl4_6
    | spl4_26
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f243,f100,f246,f108])).

fof(f100,plain,
    ( spl4_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f243,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(superposition,[],[f101,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f101,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f222,plain,
    ( ~ spl4_12
    | ~ spl4_8
    | spl4_17 ),
    inference(avatar_split_clause,[],[f220,f198,f116,f137])).

fof(f116,plain,
    ( spl4_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f198,plain,
    ( spl4_17
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f220,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_17 ),
    inference(resolution,[],[f199,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f199,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f198])).

fof(f219,plain,
    ( ~ spl4_12
    | ~ spl4_8
    | spl4_22
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f215,f104,f217,f116,f137])).

fof(f217,plain,
    ( spl4_22
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f104,plain,
    ( spl4_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f215,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f64,f105])).

fof(f105,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f214,plain,
    ( ~ spl4_17
    | spl4_20
    | ~ spl4_21
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f196,f191,f212,f209,f198])).

fof(f191,plain,
    ( spl4_16
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f196,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_16 ),
    inference(superposition,[],[f56,f192])).

fof(f192,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f191])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f207,plain,
    ( ~ spl4_17
    | ~ spl4_1
    | spl4_19
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f195,f191,f205,f90,f198])).

fof(f90,plain,
    ( spl4_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f205,plain,
    ( spl4_19
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f195,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_16 ),
    inference(superposition,[],[f59,f192])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f203,plain,
    ( ~ spl4_17
    | ~ spl4_1
    | spl4_18
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f194,f191,f201,f90,f198])).

fof(f201,plain,
    ( spl4_18
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f194,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_16 ),
    inference(superposition,[],[f60,f192])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f193,plain,
    ( ~ spl4_12
    | ~ spl4_8
    | spl4_16
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f189,f104,f191,f116,f137])).

fof(f189,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f63,f105])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f153,plain,
    ( ~ spl4_6
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl4_6
    | spl4_12 ),
    inference(subsumption_resolution,[],[f109,f151])).

fof(f151,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_12 ),
    inference(resolution,[],[f73,f138])).

fof(f138,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f147,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f144,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f144,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_13
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f145,plain,
    ( ~ spl4_13
    | spl4_11 ),
    inference(avatar_split_clause,[],[f141,f128,f143])).

fof(f128,plain,
    ( spl4_11
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f141,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_11 ),
    inference(resolution,[],[f65,f129])).

fof(f129,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f140,plain,
    ( ~ spl4_12
    | ~ spl4_8
    | spl4_1 ),
    inference(avatar_split_clause,[],[f135,f90,f116,f137])).

fof(f135,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(resolution,[],[f62,f91])).

fof(f91,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f122,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f52,f120])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f118,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f46,f116])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f39])).

fof(f39,plain,
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

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f114,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f47,f112])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f110,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f48,f108])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f106,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f49,f104])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f50,f100])).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f51,f96,f93,f90])).

fof(f51,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:57:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (8742)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (8751)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (8743)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (8742)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (8749)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (8751)Refutation not found, incomplete strategy% (8751)------------------------------
% 0.21/0.49  % (8751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8751)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (8751)Memory used [KB]: 6268
% 0.21/0.49  % (8751)Time elapsed: 0.013 s
% 0.21/0.49  % (8751)------------------------------
% 0.21/0.49  % (8751)------------------------------
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f459,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f98,f102,f106,f110,f114,f118,f122,f140,f145,f147,f153,f193,f203,f207,f214,f219,f222,f249,f270,f282,f349,f351,f355,f368,f375,f376,f383,f454])).
% 0.21/0.49  fof(f454,plain,(
% 0.21/0.49    ~spl4_9 | spl4_41),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f452])).
% 0.21/0.49  fof(f452,plain,(
% 0.21/0.49    $false | (~spl4_9 | spl4_41)),
% 0.21/0.49    inference(resolution,[],[f382,f181])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ( ! [X2] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) ) | ~spl4_9),
% 0.21/0.49    inference(superposition,[],[f72,f157])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = sK3(k1_xboole_0,X1)) ) | ~spl4_9),
% 0.21/0.49    inference(resolution,[],[f154,f150])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ( ! [X1] : (m1_subset_1(sK3(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.49    inference(superposition,[],[f69,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(flattening,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_9),
% 0.21/0.49    inference(resolution,[],[f148,f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl4_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(resolution,[],[f55,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f382,plain,(
% 0.21/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl4_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f381])).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    spl4_41 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.49  fof(f383,plain,(
% 0.21/0.49    ~spl4_41 | spl4_2 | ~spl4_30 | ~spl4_33 | ~spl4_37),
% 0.21/0.49    inference(avatar_split_clause,[],[f379,f358,f280,f268,f93,f381])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl4_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    spl4_30 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    spl4_33 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.49  fof(f358,plain,(
% 0.21/0.49    spl4_37 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.49  fof(f379,plain,(
% 0.21/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl4_2 | ~spl4_30 | ~spl4_33 | ~spl4_37)),
% 0.21/0.49    inference(forward_demodulation,[],[f378,f359])).
% 0.21/0.49  fof(f359,plain,(
% 0.21/0.49    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl4_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f358])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl4_2 | ~spl4_30 | ~spl4_33)),
% 0.21/0.49    inference(forward_demodulation,[],[f377,f281])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~spl4_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f280])).
% 0.21/0.49  fof(f377,plain,(
% 0.21/0.49    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl4_2 | ~spl4_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f94,f347])).
% 0.21/0.49  fof(f347,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl4_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f268])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f376,plain,(
% 0.21/0.49    k1_xboole_0 != k2_funct_1(sK2) | k1_xboole_0 != sK2 | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    ~spl4_40 | spl4_3 | ~spl4_30 | ~spl4_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f371,f280,f268,f96,f373])).
% 0.21/0.49  fof(f373,plain,(
% 0.21/0.49    spl4_40 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl4_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f371,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_30 | ~spl4_33)),
% 0.21/0.49    inference(forward_demodulation,[],[f370,f281])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f369,f83])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_3 | ~spl4_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f97,f347])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    spl4_37 | ~spl4_20 | ~spl4_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f367,f280,f209,f358])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    spl4_20 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl4_20 | ~spl4_33)),
% 0.21/0.49    inference(forward_demodulation,[],[f210,f281])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    k1_xboole_0 = k2_funct_1(sK2) | ~spl4_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f209])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    sK1 != k2_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | sK0 != k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f351,plain,(
% 0.21/0.49    sK1 != k2_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | sK0 != k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f349,plain,(
% 0.21/0.49    spl4_36 | spl4_30 | ~spl4_7 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f339,f108,f112,f268,f345])).
% 0.21/0.49  fof(f345,plain,(
% 0.21/0.49    spl4_36 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl4_7 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relat_1(sK2) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f310,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | k1_relat_1(X5) = X3) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f307])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.49    inference(superposition,[],[f76,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ~spl4_12 | spl4_33 | ~spl4_30 | ~spl4_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f258,f246,f268,f280,f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl4_12 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    spl4_26 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl4_26),
% 0.21/0.49    inference(superposition,[],[f57,f247])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    sK1 = k2_relat_1(sK2) | ~spl4_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f246])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  % (8749)Refutation not found, incomplete strategy% (8749)------------------------------
% 0.21/0.49  % (8749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    ~spl4_30 | spl4_21 | ~spl4_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f255,f246,f212,f268])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    spl4_21 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | (spl4_21 | ~spl4_26)),
% 0.21/0.49    inference(superposition,[],[f213,f247])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(sK2) | spl4_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f212])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    ~spl4_6 | spl4_26 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f243,f100,f246,f108])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl4_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.49    inference(superposition,[],[f101,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ~spl4_12 | ~spl4_8 | spl4_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f220,f198,f116,f137])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl4_8 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    spl4_17 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_17),
% 0.21/0.49    inference(resolution,[],[f199,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ~v1_relat_1(k2_funct_1(sK2)) | spl4_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f198])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ~spl4_12 | ~spl4_8 | spl4_22 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f215,f104,f217,f116,f137])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    spl4_22 <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl4_5 <=> v2_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f64,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    v2_funct_1(sK2) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ~spl4_17 | spl4_20 | ~spl4_21 | ~spl4_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f196,f191,f212,f209,f198])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl4_16 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_16),
% 0.21/0.49    inference(superposition,[],[f56,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f191])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ~spl4_17 | ~spl4_1 | spl4_19 | ~spl4_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f195,f191,f205,f90,f198])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl4_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    spl4_19 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_16),
% 0.21/0.49    inference(superposition,[],[f59,f192])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    ~spl4_17 | ~spl4_1 | spl4_18 | ~spl4_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f194,f191,f201,f90,f198])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    spl4_18 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_16),
% 0.21/0.49    inference(superposition,[],[f60,f192])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ~spl4_12 | ~spl4_8 | spl4_16 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f189,f104,f191,f116,f137])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f63,f105])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ~spl4_6 | spl4_12),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    $false | (~spl4_6 | spl4_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f151])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_12),
% 0.21/0.49    inference(resolution,[],[f73,f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | spl4_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    spl4_13),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    $false | spl4_13),
% 0.21/0.49    inference(resolution,[],[f144,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl4_13 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ~spl4_13 | spl4_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f141,f128,f143])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl4_11 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_11),
% 0.21/0.49    inference(resolution,[],[f65,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ~spl4_12 | ~spl4_8 | spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f135,f90,f116,f137])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 0.21/0.49    inference(resolution,[],[f62,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK2)) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f120])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f116])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f16])).
% 0.21/0.49  fof(f16,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f112])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f108])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f104])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    v2_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f50,f100])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f96,f93,f90])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (8742)------------------------------
% 0.21/0.49  % (8742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8742)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (8742)Memory used [KB]: 10874
% 0.21/0.49  % (8742)Time elapsed: 0.072 s
% 0.21/0.49  % (8742)------------------------------
% 0.21/0.49  % (8742)------------------------------
% 0.21/0.50  % (8735)Success in time 0.133 s
%------------------------------------------------------------------------------
