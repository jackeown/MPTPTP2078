%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 345 expanded)
%              Number of leaves         :   34 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  476 (1057 expanded)
%              Number of equality atoms :  114 ( 233 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f416,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f77,f84,f88,f92,f112,f119,f141,f149,f163,f175,f193,f206,f226,f249,f308,f309,f344,f377,f391,f394,f411])).

fof(f411,plain,
    ( spl3_42
    | ~ spl3_46
    | ~ spl3_48 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | spl3_42
    | ~ spl3_46
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f409,f343])).

fof(f343,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl3_42 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl3_42
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f409,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl3_46
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f399,f380])).

fof(f380,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl3_46
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f399,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl3_48 ),
    inference(resolution,[],[f390,f54])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f390,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl3_48
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f394,plain,
    ( spl3_46
    | ~ spl3_25
    | ~ spl3_30
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f382,f375,f247,f224,f379])).

fof(f224,plain,
    ( spl3_25
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f247,plain,
    ( spl3_30
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f375,plain,
    ( spl3_45
  <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f382,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_25
    | ~ spl3_30
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f381,f248])).

fof(f248,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f247])).

fof(f381,plain,
    ( sK1 = k1_relset_1(sK1,k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_25
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f376,f225])).

fof(f225,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f224])).

fof(f376,plain,
    ( sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f375])).

fof(f391,plain,
    ( spl3_48
    | ~ spl3_8
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f297,f247,f224,f114,f389])).

fof(f114,plain,
    ( spl3_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f297,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f290,f225])).

fof(f290,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_8
    | ~ spl3_30 ),
    inference(superposition,[],[f205,f248])).

fof(f205,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f377,plain,
    ( spl3_45
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f218,f139,f114,f375])).

fof(f139,plain,
    ( spl3_12
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f218,plain,
    ( sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f213,f140])).

fof(f140,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f213,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl3_8 ),
    inference(resolution,[],[f205,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f344,plain,
    ( ~ spl3_42
    | spl3_9
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f294,f247,f224,f117,f342])).

fof(f117,plain,
    ( spl3_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f294,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl3_9
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f287,f225])).

fof(f287,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_9
    | ~ spl3_30 ),
    inference(superposition,[],[f118,f248])).

fof(f118,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f309,plain,
    ( k1_xboole_0 != sK0
    | sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f308,plain,
    ( spl3_30
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f264,f257,f90,f86,f79,f63,f59,f247])).

fof(f59,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f63,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f79,plain,
    ( spl3_4
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f86,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f90,plain,
    ( spl3_7
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f257,plain,
    ( spl3_33
  <=> k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f264,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f124,f258])).

fof(f258,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f257])).

fof(f124,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f122,f107])).

fof(f107,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f106,f100])).

fof(f100,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f93,f91])).

fof(f91,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f93,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f87,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f87,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f106,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f72,f94])).

fof(f94,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f87,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f72,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f69,f60])).

fof(f60,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f69,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f64,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f64,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f122,plain,
    ( k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(resolution,[],[f80,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_relat_1(X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f80,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f249,plain,
    ( spl3_29
    | spl3_30
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f103,f86,f75,f247,f244])).

fof(f244,plain,
    ( spl3_29
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f75,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f96,f76])).

fof(f76,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f96,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f87,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f226,plain,
    ( spl3_25
    | ~ spl3_8
    | spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f219,f139,f117,f114,f224])).

fof(f219,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_8
    | spl3_9
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f217,f218])).

fof(f217,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl3_8
    | spl3_9 ),
    inference(subsumption_resolution,[],[f211,f118])).

fof(f211,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f205,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f206,plain,
    ( spl3_8
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f195,f191,f147,f114])).

fof(f147,plain,
    ( spl3_14
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f191,plain,
    ( spl3_22
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f195,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f192,f148])).

fof(f148,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f192,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( spl3_22
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f104,f86,f191])).

fof(f104,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f99,f98])).

fof(f98,plain,
    ( k4_relat_1(sK2) = k3_relset_1(sK0,sK1,sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f87,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f99,plain,
    ( m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_6 ),
    inference(resolution,[],[f87,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f175,plain,
    ( spl3_19
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f97,f86,f173])).

fof(f173,plain,
    ( spl3_19
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f97,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f87,f48])).

fof(f163,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f105,f86,f63,f59,f161])).

fof(f161,plain,
    ( spl3_16
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f105,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f73,f94])).

fof(f73,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f70,f60])).

fof(f70,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f64,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f149,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f108,f86,f63,f59,f147])).

fof(f108,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f71,f94])).

fof(f71,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f68,f60])).

fof(f68,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f64,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f141,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f107,f90,f86,f63,f59,f139])).

fof(f119,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f110,f86,f59,f117,f114])).

fof(f110,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f29,f109])).

fof(f109,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f67,f94])).

fof(f67,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f29,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f112,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f94,f86,f82])).

fof(f82,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f34,f90])).

fof(f34,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f32,f86])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,
    ( spl3_4
    | ~ spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f66,f59,f82,f79])).

fof(f66,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:18:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.44  % (30254)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (30237)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (30238)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (30246)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (30249)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (30256)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (30236)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (30250)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (30237)Refutation not found, incomplete strategy% (30237)------------------------------
% 0.21/0.48  % (30237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30237)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30237)Memory used [KB]: 10618
% 0.21/0.48  % (30237)Time elapsed: 0.072 s
% 0.21/0.48  % (30237)------------------------------
% 0.21/0.48  % (30237)------------------------------
% 0.21/0.48  % (30240)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (30256)Refutation not found, incomplete strategy% (30256)------------------------------
% 0.21/0.48  % (30256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30256)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30256)Memory used [KB]: 10618
% 0.21/0.48  % (30256)Time elapsed: 0.079 s
% 0.21/0.48  % (30256)------------------------------
% 0.21/0.48  % (30256)------------------------------
% 0.21/0.48  % (30245)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (30236)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f416,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f61,f65,f77,f84,f88,f92,f112,f119,f141,f149,f163,f175,f193,f206,f226,f249,f308,f309,f344,f377,f391,f394,f411])).
% 0.21/0.48  fof(f411,plain,(
% 0.21/0.48    spl3_42 | ~spl3_46 | ~spl3_48),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f410])).
% 0.21/0.48  fof(f410,plain,(
% 0.21/0.48    $false | (spl3_42 | ~spl3_46 | ~spl3_48)),
% 0.21/0.48    inference(subsumption_resolution,[],[f409,f343])).
% 0.21/0.48  fof(f343,plain,(
% 0.21/0.48    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | spl3_42),
% 0.21/0.48    inference(avatar_component_clause,[],[f342])).
% 0.21/0.48  fof(f342,plain,(
% 0.21/0.48    spl3_42 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.48  fof(f409,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (~spl3_46 | ~spl3_48)),
% 0.21/0.48    inference(subsumption_resolution,[],[f399,f380])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | ~spl3_46),
% 0.21/0.48    inference(avatar_component_clause,[],[f379])).
% 0.21/0.48  fof(f379,plain,(
% 0.21/0.48    spl3_46 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | ~spl3_48),
% 0.21/0.48    inference(resolution,[],[f390,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f390,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_48),
% 0.21/0.48    inference(avatar_component_clause,[],[f389])).
% 0.21/0.48  fof(f389,plain,(
% 0.21/0.48    spl3_48 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.48  fof(f394,plain,(
% 0.21/0.48    spl3_46 | ~spl3_25 | ~spl3_30 | ~spl3_45),
% 0.21/0.48    inference(avatar_split_clause,[],[f382,f375,f247,f224,f379])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    spl3_25 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    spl3_30 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.48  fof(f375,plain,(
% 0.21/0.48    spl3_45 <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | (~spl3_25 | ~spl3_30 | ~spl3_45)),
% 0.21/0.48    inference(forward_demodulation,[],[f381,f248])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl3_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f247])).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    sK1 = k1_relset_1(sK1,k1_xboole_0,k2_funct_1(sK2)) | (~spl3_25 | ~spl3_45)),
% 0.21/0.48    inference(forward_demodulation,[],[f376,f225])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl3_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f224])).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~spl3_45),
% 0.21/0.48    inference(avatar_component_clause,[],[f375])).
% 0.21/0.48  fof(f391,plain,(
% 0.21/0.48    spl3_48 | ~spl3_8 | ~spl3_25 | ~spl3_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f297,f247,f224,f114,f389])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl3_8 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_8 | ~spl3_25 | ~spl3_30)),
% 0.21/0.48    inference(forward_demodulation,[],[f290,f225])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_8 | ~spl3_30)),
% 0.21/0.48    inference(superposition,[],[f205,f248])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f114])).
% 0.21/0.48  fof(f377,plain,(
% 0.21/0.48    spl3_45 | ~spl3_8 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f218,f139,f114,f375])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl3_12 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl3_8 | ~spl3_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f213,f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f139])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~spl3_8),
% 0.21/0.48    inference(resolution,[],[f205,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f344,plain,(
% 0.21/0.48    ~spl3_42 | spl3_9 | ~spl3_25 | ~spl3_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f294,f247,f224,f117,f342])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl3_9 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f294,plain,(
% 0.21/0.48    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (spl3_9 | ~spl3_25 | ~spl3_30)),
% 0.21/0.48    inference(forward_demodulation,[],[f287,f225])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_9 | ~spl3_30)),
% 0.21/0.48    inference(superposition,[],[f118,f248])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f117])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    spl3_30 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_33),
% 0.21/0.48    inference(avatar_split_clause,[],[f264,f257,f90,f86,f79,f63,f59,f247])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_4 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl3_7 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    spl3_33 <=> k1_xboole_0 = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7 | ~spl3_33)),
% 0.21/0.48    inference(subsumption_resolution,[],[f124,f258])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(k2_funct_1(sK2)) | ~spl3_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f257])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | k1_xboole_0 != k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.21/0.48    inference(forward_demodulation,[],[f122,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7)),
% 0.21/0.48    inference(forward_demodulation,[],[f106,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    sK1 = k2_relat_1(sK2) | (~spl3_6 | ~spl3_7)),
% 0.21/0.48    inference(forward_demodulation,[],[f93,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f90])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_6),
% 0.21/0.48    inference(resolution,[],[f87,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.48    inference(resolution,[],[f87,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f69,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f64,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    k1_xboole_0 != k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f80,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    v1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    spl3_29 | spl3_30 | ~spl3_3 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f103,f86,f75,f247,f244])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    spl3_29 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl3_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl3_3 | ~spl3_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl3_6),
% 0.21/0.48    inference(resolution,[],[f87,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    spl3_25 | ~spl3_8 | spl3_9 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f219,f139,f117,f114,f224])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | (~spl3_8 | spl3_9 | ~spl3_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f217,f218])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl3_8 | spl3_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f211,f118])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl3_8),
% 0.21/0.48    inference(resolution,[],[f205,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    spl3_8 | ~spl3_14 | ~spl3_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f195,f191,f147,f114])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    spl3_14 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    spl3_22 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_14 | ~spl3_22)),
% 0.21/0.48    inference(forward_demodulation,[],[f192,f148])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f147])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f191])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    spl3_22 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f104,f86,f191])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_6),
% 0.21/0.48    inference(forward_demodulation,[],[f99,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k4_relat_1(sK2) = k3_relset_1(sK0,sK1,sK2) | ~spl3_6),
% 0.21/0.48    inference(resolution,[],[f87,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_6),
% 0.21/0.48    inference(resolution,[],[f87,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    spl3_19 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f97,f86,f173])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    spl3_19 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl3_6),
% 0.21/0.48    inference(resolution,[],[f87,f48])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    spl3_16 | ~spl3_1 | ~spl3_2 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f105,f86,f63,f59,f161])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl3_16 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f94])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f60])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f64,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    spl3_14 | ~spl3_1 | ~spl3_2 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f108,f86,f63,f59,f147])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f71,f94])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f60])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f64,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = k4_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl3_12 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f107,f90,f86,f63,f59,f139])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ~spl3_8 | ~spl3_9 | ~spl3_1 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f110,f86,f59,f117,f114])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_1 | ~spl3_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f29,f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f67,f94])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.21/0.48    inference(resolution,[],[f60,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl3_5 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f94,f86,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f90])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f86])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl3_4 | ~spl3_5 | ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f66,f59,f82,f79])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.21/0.48    inference(resolution,[],[f60,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f75])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f63])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    v2_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f59])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30236)------------------------------
% 0.21/0.48  % (30236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30236)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30236)Memory used [KB]: 6396
% 0.21/0.48  % (30236)Time elapsed: 0.079 s
% 0.21/0.48  % (30236)------------------------------
% 0.21/0.48  % (30236)------------------------------
% 0.21/0.49  % (30235)Success in time 0.129 s
%------------------------------------------------------------------------------
