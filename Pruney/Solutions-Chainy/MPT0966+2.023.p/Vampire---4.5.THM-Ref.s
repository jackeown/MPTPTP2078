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
% DateTime   : Thu Dec  3 13:00:41 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  233 ( 436 expanded)
%              Number of leaves         :   48 ( 162 expanded)
%              Depth                    :   13
%              Number of atoms          :  682 (1519 expanded)
%              Number of equality atoms :  167 ( 495 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2017,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f122,f127,f136,f220,f255,f285,f304,f313,f342,f384,f519,f543,f553,f678,f689,f710,f914,f964,f970,f1158,f1215,f1548,f1560,f1585,f1604,f1624,f1692,f1805,f1831,f2016])).

fof(f2016,plain,
    ( spl6_16
    | ~ spl6_31
    | ~ spl6_74 ),
    inference(avatar_contradiction_clause,[],[f2014])).

fof(f2014,plain,
    ( $false
    | spl6_16
    | ~ spl6_31
    | ~ spl6_74 ),
    inference(unit_resulting_resolution,[],[f89,f383,f219,f1157])).

fof(f1157,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X1)
        | ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f1156])).

fof(f1156,plain,
    ( spl6_74
  <=> ! [X1,X0] :
        ( ~ r1_tarski(sK0,X1)
        | ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f219,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl6_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f383,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl6_31
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1831,plain,
    ( spl6_15
    | ~ spl6_16
    | spl6_71
    | ~ spl6_90
    | ~ spl6_93 ),
    inference(avatar_contradiction_clause,[],[f1830])).

fof(f1830,plain,
    ( $false
    | spl6_15
    | ~ spl6_16
    | spl6_71
    | ~ spl6_90
    | ~ spl6_93 ),
    inference(subsumption_resolution,[],[f1829,f969])).

fof(f969,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl6_71 ),
    inference(avatar_component_clause,[],[f967])).

fof(f967,plain,
    ( spl6_71
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f1829,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | spl6_15
    | ~ spl6_16
    | ~ spl6_90
    | ~ spl6_93 ),
    inference(forward_demodulation,[],[f1815,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f1815,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | spl6_15
    | ~ spl6_16
    | ~ spl6_90
    | ~ spl6_93 ),
    inference(backward_demodulation,[],[f1691,f1809])).

fof(f1809,plain,
    ( k1_xboole_0 = sK2
    | spl6_15
    | ~ spl6_16
    | ~ spl6_93 ),
    inference(subsumption_resolution,[],[f1808,f218])).

fof(f218,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f217])).

fof(f1808,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_15
    | ~ spl6_93 ),
    inference(subsumption_resolution,[],[f1807,f215])).

fof(f215,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl6_15
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1807,plain,
    ( v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_93 ),
    inference(trivial_inequality_removal,[],[f1806])).

fof(f1806,plain,
    ( sK0 != sK0
    | v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_93 ),
    inference(superposition,[],[f84,f1804])).

fof(f1804,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl6_93 ),
    inference(avatar_component_clause,[],[f1802])).

fof(f1802,plain,
    ( spl6_93
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f37])).

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
    inference(flattening,[],[f36])).

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

fof(f1691,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f1689])).

fof(f1689,plain,
    ( spl6_90
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f1805,plain,
    ( spl6_93
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f1795,f310,f217,f1802])).

fof(f310,plain,
    ( spl6_25
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f1795,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f1662,f312])).

fof(f312,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f310])).

fof(f1662,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f218,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1692,plain,
    ( spl6_90
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f1665,f217,f1689])).

fof(f1665,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ spl6_16 ),
    inference(resolution,[],[f218,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1624,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK3)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1604,plain,
    ( ~ spl6_21
    | spl6_27
    | ~ spl6_55
    | ~ spl6_84 ),
    inference(avatar_contradiction_clause,[],[f1603])).

fof(f1603,plain,
    ( $false
    | ~ spl6_21
    | spl6_27
    | ~ spl6_55
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f1588,f688])).

fof(f688,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f687])).

fof(f687,plain,
    ( spl6_55
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f1588,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_21
    | spl6_27
    | ~ spl6_84 ),
    inference(backward_demodulation,[],[f341,f1572])).

fof(f1572,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_21
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f1567,f276])).

fof(f276,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl6_21
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f1567,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl6_84 ),
    inference(trivial_inequality_removal,[],[f1566])).

fof(f1566,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl6_84 ),
    inference(superposition,[],[f60,f1559])).

fof(f1559,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f1557])).

fof(f1557,plain,
    ( spl6_84
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f341,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl6_27
  <=> v1_funct_2(sK3,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1585,plain,
    ( spl6_87
    | ~ spl6_69
    | ~ spl6_83 ),
    inference(avatar_split_clause,[],[f1551,f1545,f911,f1578])).

fof(f1578,plain,
    ( spl6_87
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f911,plain,
    ( spl6_69
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f1545,plain,
    ( spl6_83
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f1551,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl6_69
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f1549,f913])).

fof(f913,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f911])).

fof(f1549,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_83 ),
    inference(resolution,[],[f1547,f289])).

fof(f289,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f97,f92])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f97,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1547,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f1545])).

fof(f1560,plain,
    ( spl6_84
    | ~ spl6_7
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f1542,f310,f133,f1557])).

fof(f133,plain,
    ( spl6_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1542,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_7
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f312,f135])).

fof(f135,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1548,plain,
    ( spl6_83
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f1536,f133,f106,f1545])).

fof(f106,plain,
    ( spl6_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1536,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f108,f135])).

fof(f108,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1215,plain,
    ( spl6_7
    | ~ spl6_58
    | ~ spl6_70 ),
    inference(avatar_contradiction_clause,[],[f1214])).

fof(f1214,plain,
    ( $false
    | spl6_7
    | ~ spl6_58
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f1206,f134])).

fof(f134,plain,
    ( k1_xboole_0 != sK0
    | spl6_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1206,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_58
    | ~ spl6_70 ),
    inference(resolution,[],[f963,f709])).

fof(f709,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k1_xboole_0)
        | k1_xboole_0 = X3 )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f708])).

fof(f708,plain,
    ( spl6_58
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f963,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f961])).

fof(f961,plain,
    ( spl6_70
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f1158,plain,
    ( spl6_74
    | ~ spl6_21
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f1153,f310,f275,f1156])).

fof(f1153,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X1)
        | ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl6_21
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f286,f312])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | ~ r1_tarski(k1_relat_1(sK3),X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl6_21 ),
    inference(resolution,[],[f276,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f970,plain,
    ( ~ spl6_71
    | spl6_28 ),
    inference(avatar_split_clause,[],[f965,f344,f967])).

fof(f344,plain,
    ( spl6_28
  <=> v4_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f965,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl6_28 ),
    inference(resolution,[],[f345,f409])).

fof(f409,plain,(
    ! [X2,X3] :
      ( v4_relat_1(X2,X3)
      | ~ r1_tarski(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f191,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f80,f91])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f345,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | spl6_28 ),
    inference(avatar_component_clause,[],[f344])).

fof(f964,plain,
    ( spl6_70
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f958,f344,f310,f275,f961])).

fof(f958,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f944,f312])).

fof(f944,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f943,f276])).

fof(f943,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_28 ),
    inference(resolution,[],[f346,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f346,plain,
    ( v4_relat_1(sK3,k1_xboole_0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f344])).

fof(f914,plain,
    ( spl6_69
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f895,f129,f119,f911])).

fof(f119,plain,
    ( spl6_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f129,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f895,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f890,f91])).

fof(f890,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f121,f130])).

fof(f130,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f121,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f710,plain,
    ( spl6_58
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f706,f550,f708])).

fof(f550,plain,
    ( spl6_45
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f706,plain,
    ( ! [X3] :
        ( k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_xboole_0) )
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f705,f552])).

fof(f552,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f550])).

fof(f705,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k1_xboole_0)
        | k2_relat_1(k1_xboole_0) = X3 )
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f184,f552])).

fof(f184,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k2_relat_1(k1_xboole_0))
      | k2_relat_1(k1_xboole_0) = X3 ) ),
    inference(resolution,[],[f71,f138])).

fof(f138,plain,(
    ! [X1] : r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(superposition,[],[f65,f92])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f689,plain,
    ( spl6_55
    | ~ spl6_19
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f683,f676,f247,f687])).

fof(f247,plain,
    ( spl6_19
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f676,plain,
    ( spl6_54
  <=> ! [X1] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f683,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl6_19
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f682,f248])).

fof(f248,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f247])).

fof(f682,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_54 ),
    inference(trivial_inequality_removal,[],[f679])).

fof(f679,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_54 ),
    inference(superposition,[],[f283,f677])).

fof(f677,plain,
    ( ! [X1] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,k1_xboole_0)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f676])).

fof(f283,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f96,f92])).

fof(f96,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f678,plain,
    ( spl6_54
    | ~ spl6_19
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f674,f540,f247,f676])).

fof(f540,plain,
    ( spl6_44
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f674,plain,
    ( ! [X1] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,k1_xboole_0)
    | ~ spl6_19
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f507,f542])).

fof(f542,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f540])).

fof(f507,plain,
    ( ! [X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X1,k1_xboole_0)
    | ~ spl6_19 ),
    inference(resolution,[],[f228,f248])).

fof(f228,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relat_1(X3) = k1_relset_1(k1_xboole_0,X2,X3) ) ),
    inference(superposition,[],[f78,f92])).

fof(f553,plain,
    ( spl6_45
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f524,f516,f550])).

fof(f516,plain,
    ( spl6_42
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f524,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_42 ),
    inference(superposition,[],[f59,f518])).

fof(f518,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f516])).

fof(f59,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f543,plain,
    ( spl6_44
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f523,f516,f540])).

fof(f523,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_42 ),
    inference(superposition,[],[f58,f518])).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f519,plain,(
    spl6_42 ),
    inference(avatar_split_clause,[],[f489,f516])).

fof(f489,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f485])).

fof(f485,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f163,f450])).

fof(f450,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(resolution,[],[f154,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f62,f64])).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f163,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_relat_1(X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f60,f58])).

fof(f384,plain,
    ( spl6_31
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f369,f124,f119,f381])).

fof(f124,plain,
    ( spl6_5
  <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f369,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f126,f230])).

fof(f230,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f79,f121])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f126,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f342,plain,
    ( ~ spl6_27
    | ~ spl6_7
    | spl6_15 ),
    inference(avatar_split_clause,[],[f323,f213,f133,f339])).

fof(f323,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl6_7
    | spl6_15 ),
    inference(backward_demodulation,[],[f215,f135])).

fof(f313,plain,
    ( spl6_25
    | ~ spl6_4
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f307,f301,f119,f310])).

fof(f301,plain,
    ( spl6_24
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f307,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_4
    | ~ spl6_24 ),
    inference(forward_demodulation,[],[f224,f303])).

fof(f303,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f301])).

fof(f224,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f78,f121])).

fof(f304,plain,
    ( spl6_24
    | ~ spl6_2
    | ~ spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f299,f129,f119,f106,f301])).

fof(f299,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_2
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f298,f121])).

fof(f298,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_2
    | spl6_6 ),
    inference(subsumption_resolution,[],[f296,f131])).

fof(f131,plain,
    ( k1_xboole_0 != sK1
    | spl6_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f296,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_2 ),
    inference(resolution,[],[f82,f108])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f285,plain,
    ( ~ spl6_4
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl6_4
    | spl6_21 ),
    inference(unit_resulting_resolution,[],[f64,f121,f277,f62])).

fof(f277,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f275])).

fof(f255,plain,(
    spl6_19 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl6_19 ),
    inference(subsumption_resolution,[],[f252,f89])).

fof(f252,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_19 ),
    inference(resolution,[],[f249,f73])).

fof(f249,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f247])).

fof(f220,plain,
    ( ~ spl6_15
    | ~ spl6_16
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f211,f101,f217,f213])).

fof(f101,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f211,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f55,f103])).

fof(f103,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f55,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f136,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f54,f133,f129])).

fof(f54,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f127,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f53,f124])).

fof(f53,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f122,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f52,f119])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f109,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f51,f106])).

fof(f51,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f50,f101])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:11:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (7294)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (7304)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (7295)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (7298)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (7297)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (7305)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (7310)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (7296)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (7306)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (7298)Refutation not found, incomplete strategy% (7298)------------------------------
% 0.21/0.51  % (7298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7298)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7298)Memory used [KB]: 10618
% 0.21/0.51  % (7298)Time elapsed: 0.106 s
% 0.21/0.51  % (7298)------------------------------
% 0.21/0.51  % (7298)------------------------------
% 0.21/0.52  % (7314)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (7297)Refutation not found, incomplete strategy% (7297)------------------------------
% 0.21/0.52  % (7297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7297)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7297)Memory used [KB]: 6140
% 0.21/0.52  % (7297)Time elapsed: 0.106 s
% 0.21/0.52  % (7297)------------------------------
% 0.21/0.52  % (7297)------------------------------
% 0.21/0.52  % (7307)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (7302)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (7313)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (7311)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (7299)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (7312)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (7293)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (7293)Refutation not found, incomplete strategy% (7293)------------------------------
% 0.21/0.53  % (7293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7293)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7293)Memory used [KB]: 10618
% 0.21/0.53  % (7293)Time elapsed: 0.114 s
% 0.21/0.53  % (7293)------------------------------
% 0.21/0.53  % (7293)------------------------------
% 0.21/0.53  % (7292)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (7315)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (7316)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (7300)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (7308)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.56  % (7303)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.57  % (7317)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.78/0.60  % (7309)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.78/0.61  % (7301)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 2.00/0.61  % (7294)Refutation found. Thanks to Tanya!
% 2.00/0.61  % SZS status Theorem for theBenchmark
% 2.00/0.61  % SZS output start Proof for theBenchmark
% 2.00/0.62  fof(f2017,plain,(
% 2.00/0.62    $false),
% 2.00/0.62    inference(avatar_sat_refutation,[],[f104,f109,f122,f127,f136,f220,f255,f285,f304,f313,f342,f384,f519,f543,f553,f678,f689,f710,f914,f964,f970,f1158,f1215,f1548,f1560,f1585,f1604,f1624,f1692,f1805,f1831,f2016])).
% 2.00/0.62  fof(f2016,plain,(
% 2.00/0.62    spl6_16 | ~spl6_31 | ~spl6_74),
% 2.00/0.62    inference(avatar_contradiction_clause,[],[f2014])).
% 2.00/0.62  fof(f2014,plain,(
% 2.00/0.62    $false | (spl6_16 | ~spl6_31 | ~spl6_74)),
% 2.00/0.62    inference(unit_resulting_resolution,[],[f89,f383,f219,f1157])).
% 2.00/0.62  fof(f1157,plain,(
% 2.00/0.62    ( ! [X0,X1] : (~r1_tarski(sK0,X1) | ~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl6_74),
% 2.00/0.62    inference(avatar_component_clause,[],[f1156])).
% 2.00/0.62  fof(f1156,plain,(
% 2.00/0.62    spl6_74 <=> ! [X1,X0] : (~r1_tarski(sK0,X1) | ~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 2.00/0.62  fof(f219,plain,(
% 2.00/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_16),
% 2.00/0.62    inference(avatar_component_clause,[],[f217])).
% 2.00/0.62  fof(f217,plain,(
% 2.00/0.62    spl6_16 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.00/0.62  fof(f383,plain,(
% 2.00/0.62    r1_tarski(k2_relat_1(sK3),sK2) | ~spl6_31),
% 2.00/0.62    inference(avatar_component_clause,[],[f381])).
% 2.00/0.62  fof(f381,plain,(
% 2.00/0.62    spl6_31 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 2.00/0.62  fof(f89,plain,(
% 2.00/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.00/0.62    inference(equality_resolution,[],[f70])).
% 2.00/0.62  fof(f70,plain,(
% 2.00/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.00/0.62    inference(cnf_transformation,[],[f45])).
% 2.00/0.62  fof(f45,plain,(
% 2.00/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.00/0.62    inference(flattening,[],[f44])).
% 2.00/0.62  fof(f44,plain,(
% 2.00/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.00/0.62    inference(nnf_transformation,[],[f2])).
% 2.00/0.62  fof(f2,axiom,(
% 2.00/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.00/0.62  fof(f1831,plain,(
% 2.00/0.62    spl6_15 | ~spl6_16 | spl6_71 | ~spl6_90 | ~spl6_93),
% 2.00/0.62    inference(avatar_contradiction_clause,[],[f1830])).
% 2.00/0.62  fof(f1830,plain,(
% 2.00/0.62    $false | (spl6_15 | ~spl6_16 | spl6_71 | ~spl6_90 | ~spl6_93)),
% 2.00/0.62    inference(subsumption_resolution,[],[f1829,f969])).
% 2.00/0.62  fof(f969,plain,(
% 2.00/0.62    ~r1_tarski(sK3,k1_xboole_0) | spl6_71),
% 2.00/0.62    inference(avatar_component_clause,[],[f967])).
% 2.00/0.62  fof(f967,plain,(
% 2.00/0.62    spl6_71 <=> r1_tarski(sK3,k1_xboole_0)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 2.00/0.62  fof(f1829,plain,(
% 2.00/0.62    r1_tarski(sK3,k1_xboole_0) | (spl6_15 | ~spl6_16 | ~spl6_90 | ~spl6_93)),
% 2.00/0.62    inference(forward_demodulation,[],[f1815,f91])).
% 2.00/0.62  fof(f91,plain,(
% 2.00/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.00/0.62    inference(equality_resolution,[],[f76])).
% 2.00/0.62  fof(f76,plain,(
% 2.00/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.00/0.62    inference(cnf_transformation,[],[f48])).
% 2.00/0.62  fof(f48,plain,(
% 2.00/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.00/0.62    inference(flattening,[],[f47])).
% 2.00/0.62  fof(f47,plain,(
% 2.00/0.62    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.00/0.62    inference(nnf_transformation,[],[f5])).
% 2.00/0.62  fof(f5,axiom,(
% 2.00/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.00/0.62  fof(f1815,plain,(
% 2.00/0.62    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (spl6_15 | ~spl6_16 | ~spl6_90 | ~spl6_93)),
% 2.00/0.62    inference(backward_demodulation,[],[f1691,f1809])).
% 2.00/0.62  fof(f1809,plain,(
% 2.00/0.62    k1_xboole_0 = sK2 | (spl6_15 | ~spl6_16 | ~spl6_93)),
% 2.00/0.62    inference(subsumption_resolution,[],[f1808,f218])).
% 2.00/0.62  fof(f218,plain,(
% 2.00/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_16),
% 2.00/0.62    inference(avatar_component_clause,[],[f217])).
% 2.00/0.62  fof(f1808,plain,(
% 2.00/0.62    k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (spl6_15 | ~spl6_93)),
% 2.00/0.62    inference(subsumption_resolution,[],[f1807,f215])).
% 2.00/0.62  fof(f215,plain,(
% 2.00/0.62    ~v1_funct_2(sK3,sK0,sK2) | spl6_15),
% 2.00/0.62    inference(avatar_component_clause,[],[f213])).
% 2.00/0.62  fof(f213,plain,(
% 2.00/0.62    spl6_15 <=> v1_funct_2(sK3,sK0,sK2)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.00/0.62  fof(f1807,plain,(
% 2.00/0.62    v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_93),
% 2.00/0.62    inference(trivial_inequality_removal,[],[f1806])).
% 2.00/0.62  fof(f1806,plain,(
% 2.00/0.62    sK0 != sK0 | v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_93),
% 2.00/0.62    inference(superposition,[],[f84,f1804])).
% 2.00/0.62  fof(f1804,plain,(
% 2.00/0.62    sK0 = k1_relset_1(sK0,sK2,sK3) | ~spl6_93),
% 2.00/0.62    inference(avatar_component_clause,[],[f1802])).
% 2.00/0.62  fof(f1802,plain,(
% 2.00/0.62    spl6_93 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 2.00/0.62  fof(f84,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f49])).
% 2.00/0.62  fof(f49,plain,(
% 2.00/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.62    inference(nnf_transformation,[],[f37])).
% 2.00/0.62  fof(f37,plain,(
% 2.00/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.62    inference(flattening,[],[f36])).
% 2.00/0.62  fof(f36,plain,(
% 2.00/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.62    inference(ennf_transformation,[],[f19])).
% 2.00/0.62  fof(f19,axiom,(
% 2.00/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.00/0.62  fof(f1691,plain,(
% 2.00/0.62    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | ~spl6_90),
% 2.00/0.62    inference(avatar_component_clause,[],[f1689])).
% 2.00/0.62  fof(f1689,plain,(
% 2.00/0.62    spl6_90 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).
% 2.00/0.62  fof(f1805,plain,(
% 2.00/0.62    spl6_93 | ~spl6_16 | ~spl6_25),
% 2.00/0.62    inference(avatar_split_clause,[],[f1795,f310,f217,f1802])).
% 2.00/0.62  fof(f310,plain,(
% 2.00/0.62    spl6_25 <=> sK0 = k1_relat_1(sK3)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 2.00/0.62  fof(f1795,plain,(
% 2.00/0.62    sK0 = k1_relset_1(sK0,sK2,sK3) | (~spl6_16 | ~spl6_25)),
% 2.00/0.62    inference(forward_demodulation,[],[f1662,f312])).
% 2.00/0.62  fof(f312,plain,(
% 2.00/0.62    sK0 = k1_relat_1(sK3) | ~spl6_25),
% 2.00/0.62    inference(avatar_component_clause,[],[f310])).
% 2.00/0.62  fof(f1662,plain,(
% 2.00/0.62    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl6_16),
% 2.00/0.62    inference(resolution,[],[f218,f78])).
% 2.00/0.62  fof(f78,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f33])).
% 2.00/0.62  fof(f33,plain,(
% 2.00/0.62    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.62    inference(ennf_transformation,[],[f15])).
% 2.00/0.62  fof(f15,axiom,(
% 2.00/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.00/0.62  fof(f1692,plain,(
% 2.00/0.62    spl6_90 | ~spl6_16),
% 2.00/0.62    inference(avatar_split_clause,[],[f1665,f217,f1689])).
% 2.00/0.62  fof(f1665,plain,(
% 2.00/0.62    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | ~spl6_16),
% 2.00/0.62    inference(resolution,[],[f218,f72])).
% 2.00/0.62  fof(f72,plain,(
% 2.00/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f46])).
% 2.00/0.62  fof(f46,plain,(
% 2.00/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.00/0.62    inference(nnf_transformation,[],[f6])).
% 2.00/0.62  fof(f6,axiom,(
% 2.00/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.00/0.62  fof(f1624,plain,(
% 2.00/0.62    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK3) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.00/0.62    introduced(theory_tautology_sat_conflict,[])).
% 2.00/0.62  fof(f1604,plain,(
% 2.00/0.62    ~spl6_21 | spl6_27 | ~spl6_55 | ~spl6_84),
% 2.00/0.62    inference(avatar_contradiction_clause,[],[f1603])).
% 2.00/0.62  fof(f1603,plain,(
% 2.00/0.62    $false | (~spl6_21 | spl6_27 | ~spl6_55 | ~spl6_84)),
% 2.00/0.62    inference(subsumption_resolution,[],[f1588,f688])).
% 2.00/0.62  fof(f688,plain,(
% 2.00/0.62    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl6_55),
% 2.00/0.62    inference(avatar_component_clause,[],[f687])).
% 2.00/0.62  fof(f687,plain,(
% 2.00/0.62    spl6_55 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 2.00/0.62  fof(f1588,plain,(
% 2.00/0.62    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (~spl6_21 | spl6_27 | ~spl6_84)),
% 2.00/0.62    inference(backward_demodulation,[],[f341,f1572])).
% 2.00/0.62  fof(f1572,plain,(
% 2.00/0.62    k1_xboole_0 = sK3 | (~spl6_21 | ~spl6_84)),
% 2.00/0.62    inference(subsumption_resolution,[],[f1567,f276])).
% 2.00/0.62  fof(f276,plain,(
% 2.00/0.62    v1_relat_1(sK3) | ~spl6_21),
% 2.00/0.62    inference(avatar_component_clause,[],[f275])).
% 2.00/0.62  fof(f275,plain,(
% 2.00/0.62    spl6_21 <=> v1_relat_1(sK3)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.00/0.62  fof(f1567,plain,(
% 2.00/0.62    k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl6_84),
% 2.00/0.62    inference(trivial_inequality_removal,[],[f1566])).
% 2.00/0.62  fof(f1566,plain,(
% 2.00/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl6_84),
% 2.00/0.62    inference(superposition,[],[f60,f1559])).
% 2.00/0.62  fof(f1559,plain,(
% 2.00/0.62    k1_xboole_0 = k1_relat_1(sK3) | ~spl6_84),
% 2.00/0.62    inference(avatar_component_clause,[],[f1557])).
% 2.00/0.62  fof(f1557,plain,(
% 2.00/0.62    spl6_84 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).
% 2.00/0.62  fof(f60,plain,(
% 2.00/0.62    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f25])).
% 2.00/0.62  fof(f25,plain,(
% 2.00/0.62    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.00/0.62    inference(flattening,[],[f24])).
% 2.00/0.62  fof(f24,plain,(
% 2.00/0.62    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.00/0.62    inference(ennf_transformation,[],[f12])).
% 2.00/0.62  fof(f12,axiom,(
% 2.00/0.62    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.00/0.62  fof(f341,plain,(
% 2.00/0.62    ~v1_funct_2(sK3,k1_xboole_0,sK2) | spl6_27),
% 2.00/0.62    inference(avatar_component_clause,[],[f339])).
% 2.00/0.62  fof(f339,plain,(
% 2.00/0.62    spl6_27 <=> v1_funct_2(sK3,k1_xboole_0,sK2)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 2.00/0.62  fof(f1585,plain,(
% 2.00/0.62    spl6_87 | ~spl6_69 | ~spl6_83),
% 2.00/0.62    inference(avatar_split_clause,[],[f1551,f1545,f911,f1578])).
% 2.00/0.62  fof(f1578,plain,(
% 2.00/0.62    spl6_87 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 2.00/0.62  fof(f911,plain,(
% 2.00/0.62    spl6_69 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 2.00/0.62  fof(f1545,plain,(
% 2.00/0.62    spl6_83 <=> v1_funct_2(sK3,k1_xboole_0,sK1)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 2.00/0.62  fof(f1551,plain,(
% 2.00/0.62    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | (~spl6_69 | ~spl6_83)),
% 2.00/0.62    inference(subsumption_resolution,[],[f1549,f913])).
% 2.00/0.62  fof(f913,plain,(
% 2.00/0.62    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_69),
% 2.00/0.62    inference(avatar_component_clause,[],[f911])).
% 2.00/0.62  fof(f1549,plain,(
% 2.00/0.62    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_83),
% 2.00/0.62    inference(resolution,[],[f1547,f289])).
% 2.00/0.62  fof(f289,plain,(
% 2.00/0.62    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 2.00/0.62    inference(forward_demodulation,[],[f97,f92])).
% 2.00/0.62  fof(f92,plain,(
% 2.00/0.62    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.00/0.62    inference(equality_resolution,[],[f75])).
% 2.00/0.62  fof(f75,plain,(
% 2.00/0.62    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.00/0.62    inference(cnf_transformation,[],[f48])).
% 2.00/0.62  fof(f97,plain,(
% 2.00/0.62    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.00/0.62    inference(equality_resolution,[],[f83])).
% 2.00/0.62  fof(f83,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f49])).
% 2.00/0.62  fof(f1547,plain,(
% 2.00/0.62    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl6_83),
% 2.00/0.62    inference(avatar_component_clause,[],[f1545])).
% 2.00/0.62  fof(f1560,plain,(
% 2.00/0.62    spl6_84 | ~spl6_7 | ~spl6_25),
% 2.00/0.62    inference(avatar_split_clause,[],[f1542,f310,f133,f1557])).
% 2.00/0.62  fof(f133,plain,(
% 2.00/0.62    spl6_7 <=> k1_xboole_0 = sK0),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.00/0.62  fof(f1542,plain,(
% 2.00/0.62    k1_xboole_0 = k1_relat_1(sK3) | (~spl6_7 | ~spl6_25)),
% 2.00/0.62    inference(forward_demodulation,[],[f312,f135])).
% 2.00/0.62  fof(f135,plain,(
% 2.00/0.62    k1_xboole_0 = sK0 | ~spl6_7),
% 2.00/0.62    inference(avatar_component_clause,[],[f133])).
% 2.00/0.62  fof(f1548,plain,(
% 2.00/0.62    spl6_83 | ~spl6_2 | ~spl6_7),
% 2.00/0.62    inference(avatar_split_clause,[],[f1536,f133,f106,f1545])).
% 2.00/0.62  fof(f106,plain,(
% 2.00/0.62    spl6_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.00/0.62  fof(f1536,plain,(
% 2.00/0.62    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl6_2 | ~spl6_7)),
% 2.00/0.62    inference(forward_demodulation,[],[f108,f135])).
% 2.00/0.62  fof(f108,plain,(
% 2.00/0.62    v1_funct_2(sK3,sK0,sK1) | ~spl6_2),
% 2.00/0.62    inference(avatar_component_clause,[],[f106])).
% 2.00/0.62  fof(f1215,plain,(
% 2.00/0.62    spl6_7 | ~spl6_58 | ~spl6_70),
% 2.00/0.62    inference(avatar_contradiction_clause,[],[f1214])).
% 2.00/0.62  fof(f1214,plain,(
% 2.00/0.62    $false | (spl6_7 | ~spl6_58 | ~spl6_70)),
% 2.00/0.62    inference(subsumption_resolution,[],[f1206,f134])).
% 2.00/0.62  fof(f134,plain,(
% 2.00/0.62    k1_xboole_0 != sK0 | spl6_7),
% 2.00/0.62    inference(avatar_component_clause,[],[f133])).
% 2.00/0.62  fof(f1206,plain,(
% 2.00/0.62    k1_xboole_0 = sK0 | (~spl6_58 | ~spl6_70)),
% 2.00/0.62    inference(resolution,[],[f963,f709])).
% 2.00/0.62  fof(f709,plain,(
% 2.00/0.62    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) ) | ~spl6_58),
% 2.00/0.62    inference(avatar_component_clause,[],[f708])).
% 2.00/0.62  fof(f708,plain,(
% 2.00/0.62    spl6_58 <=> ! [X3] : (k1_xboole_0 = X3 | ~r1_tarski(X3,k1_xboole_0))),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 2.00/0.62  fof(f963,plain,(
% 2.00/0.62    r1_tarski(sK0,k1_xboole_0) | ~spl6_70),
% 2.00/0.62    inference(avatar_component_clause,[],[f961])).
% 2.00/0.62  fof(f961,plain,(
% 2.00/0.62    spl6_70 <=> r1_tarski(sK0,k1_xboole_0)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 2.00/0.62  fof(f1158,plain,(
% 2.00/0.62    spl6_74 | ~spl6_21 | ~spl6_25),
% 2.00/0.62    inference(avatar_split_clause,[],[f1153,f310,f275,f1156])).
% 2.00/0.62  fof(f1153,plain,(
% 2.00/0.62    ( ! [X0,X1] : (~r1_tarski(sK0,X1) | ~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl6_21 | ~spl6_25)),
% 2.00/0.62    inference(forward_demodulation,[],[f286,f312])).
% 2.00/0.62  fof(f286,plain,(
% 2.00/0.62    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),X0) | ~r1_tarski(k1_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl6_21),
% 2.00/0.62    inference(resolution,[],[f276,f77])).
% 2.00/0.62  fof(f77,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f32])).
% 2.00/0.62  fof(f32,plain,(
% 2.00/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.00/0.62    inference(flattening,[],[f31])).
% 2.00/0.62  fof(f31,plain,(
% 2.00/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.00/0.62    inference(ennf_transformation,[],[f17])).
% 2.00/0.62  fof(f17,axiom,(
% 2.00/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 2.00/0.62  fof(f970,plain,(
% 2.00/0.62    ~spl6_71 | spl6_28),
% 2.00/0.62    inference(avatar_split_clause,[],[f965,f344,f967])).
% 2.00/0.62  fof(f344,plain,(
% 2.00/0.62    spl6_28 <=> v4_relat_1(sK3,k1_xboole_0)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 2.00/0.62  fof(f965,plain,(
% 2.00/0.62    ~r1_tarski(sK3,k1_xboole_0) | spl6_28),
% 2.00/0.62    inference(resolution,[],[f345,f409])).
% 2.00/0.62  fof(f409,plain,(
% 2.00/0.62    ( ! [X2,X3] : (v4_relat_1(X2,X3) | ~r1_tarski(X2,k1_xboole_0)) )),
% 2.00/0.62    inference(resolution,[],[f191,f73])).
% 2.00/0.62  fof(f73,plain,(
% 2.00/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f46])).
% 2.00/0.62  fof(f191,plain,(
% 2.00/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 2.00/0.62    inference(superposition,[],[f80,f91])).
% 2.00/0.62  fof(f80,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f35])).
% 2.00/0.62  fof(f35,plain,(
% 2.00/0.62    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.62    inference(ennf_transformation,[],[f14])).
% 2.00/0.62  fof(f14,axiom,(
% 2.00/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.00/0.62  fof(f345,plain,(
% 2.00/0.62    ~v4_relat_1(sK3,k1_xboole_0) | spl6_28),
% 2.00/0.62    inference(avatar_component_clause,[],[f344])).
% 2.00/0.62  fof(f964,plain,(
% 2.00/0.62    spl6_70 | ~spl6_21 | ~spl6_25 | ~spl6_28),
% 2.00/0.62    inference(avatar_split_clause,[],[f958,f344,f310,f275,f961])).
% 2.00/0.62  fof(f958,plain,(
% 2.00/0.62    r1_tarski(sK0,k1_xboole_0) | (~spl6_21 | ~spl6_25 | ~spl6_28)),
% 2.00/0.62    inference(forward_demodulation,[],[f944,f312])).
% 2.00/0.62  fof(f944,plain,(
% 2.00/0.62    r1_tarski(k1_relat_1(sK3),k1_xboole_0) | (~spl6_21 | ~spl6_28)),
% 2.00/0.62    inference(subsumption_resolution,[],[f943,f276])).
% 2.00/0.62  fof(f943,plain,(
% 2.00/0.62    r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~v1_relat_1(sK3) | ~spl6_28),
% 2.00/0.62    inference(resolution,[],[f346,f67])).
% 2.00/0.62  fof(f67,plain,(
% 2.00/0.62    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f43])).
% 2.00/0.62  fof(f43,plain,(
% 2.00/0.62    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.00/0.62    inference(nnf_transformation,[],[f30])).
% 2.00/0.62  fof(f30,plain,(
% 2.00/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.00/0.62    inference(ennf_transformation,[],[f9])).
% 2.00/0.62  fof(f9,axiom,(
% 2.00/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.00/0.62  fof(f346,plain,(
% 2.00/0.62    v4_relat_1(sK3,k1_xboole_0) | ~spl6_28),
% 2.00/0.62    inference(avatar_component_clause,[],[f344])).
% 2.00/0.62  fof(f914,plain,(
% 2.00/0.62    spl6_69 | ~spl6_4 | ~spl6_6),
% 2.00/0.62    inference(avatar_split_clause,[],[f895,f129,f119,f911])).
% 2.00/0.62  fof(f119,plain,(
% 2.00/0.62    spl6_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.00/0.62  fof(f129,plain,(
% 2.00/0.62    spl6_6 <=> k1_xboole_0 = sK1),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.00/0.62  fof(f895,plain,(
% 2.00/0.62    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_4 | ~spl6_6)),
% 2.00/0.62    inference(forward_demodulation,[],[f890,f91])).
% 2.00/0.62  fof(f890,plain,(
% 2.00/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_4 | ~spl6_6)),
% 2.00/0.62    inference(backward_demodulation,[],[f121,f130])).
% 2.00/0.62  fof(f130,plain,(
% 2.00/0.62    k1_xboole_0 = sK1 | ~spl6_6),
% 2.00/0.62    inference(avatar_component_clause,[],[f129])).
% 2.00/0.62  fof(f121,plain,(
% 2.00/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_4),
% 2.00/0.62    inference(avatar_component_clause,[],[f119])).
% 2.00/0.62  fof(f710,plain,(
% 2.00/0.62    spl6_58 | ~spl6_45),
% 2.00/0.62    inference(avatar_split_clause,[],[f706,f550,f708])).
% 2.00/0.62  fof(f550,plain,(
% 2.00/0.62    spl6_45 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 2.00/0.62  fof(f706,plain,(
% 2.00/0.62    ( ! [X3] : (k1_xboole_0 = X3 | ~r1_tarski(X3,k1_xboole_0)) ) | ~spl6_45),
% 2.00/0.62    inference(forward_demodulation,[],[f705,f552])).
% 2.00/0.62  fof(f552,plain,(
% 2.00/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_45),
% 2.00/0.62    inference(avatar_component_clause,[],[f550])).
% 2.00/0.62  fof(f705,plain,(
% 2.00/0.62    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k2_relat_1(k1_xboole_0) = X3) ) | ~spl6_45),
% 2.00/0.62    inference(forward_demodulation,[],[f184,f552])).
% 2.00/0.62  fof(f184,plain,(
% 2.00/0.62    ( ! [X3] : (~r1_tarski(X3,k2_relat_1(k1_xboole_0)) | k2_relat_1(k1_xboole_0) = X3) )),
% 2.00/0.62    inference(resolution,[],[f71,f138])).
% 2.00/0.62  fof(f138,plain,(
% 2.00/0.62    ( ! [X1] : (r1_tarski(k2_relat_1(k1_xboole_0),X1)) )),
% 2.00/0.62    inference(superposition,[],[f65,f92])).
% 2.00/0.62  fof(f65,plain,(
% 2.00/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f11])).
% 2.00/0.62  fof(f11,axiom,(
% 2.00/0.62    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).
% 2.00/0.62  fof(f71,plain,(
% 2.00/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.00/0.62    inference(cnf_transformation,[],[f45])).
% 2.00/0.62  fof(f689,plain,(
% 2.00/0.62    spl6_55 | ~spl6_19 | ~spl6_54),
% 2.00/0.62    inference(avatar_split_clause,[],[f683,f676,f247,f687])).
% 2.00/0.62  fof(f247,plain,(
% 2.00/0.62    spl6_19 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 2.00/0.62  fof(f676,plain,(
% 2.00/0.62    spl6_54 <=> ! [X1] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,k1_xboole_0)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 2.00/0.62  fof(f683,plain,(
% 2.00/0.62    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl6_19 | ~spl6_54)),
% 2.00/0.62    inference(subsumption_resolution,[],[f682,f248])).
% 2.00/0.62  fof(f248,plain,(
% 2.00/0.62    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl6_19),
% 2.00/0.62    inference(avatar_component_clause,[],[f247])).
% 2.00/0.62  fof(f682,plain,(
% 2.00/0.62    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl6_54),
% 2.00/0.62    inference(trivial_inequality_removal,[],[f679])).
% 2.00/0.62  fof(f679,plain,(
% 2.00/0.62    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl6_54),
% 2.00/0.62    inference(superposition,[],[f283,f677])).
% 2.00/0.62  fof(f677,plain,(
% 2.00/0.62    ( ! [X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,k1_xboole_0)) ) | ~spl6_54),
% 2.00/0.62    inference(avatar_component_clause,[],[f676])).
% 2.00/0.62  fof(f283,plain,(
% 2.00/0.62    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 2.00/0.62    inference(forward_demodulation,[],[f96,f92])).
% 2.00/0.62  fof(f96,plain,(
% 2.00/0.62    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.00/0.62    inference(equality_resolution,[],[f85])).
% 2.00/0.62  fof(f85,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f49])).
% 2.00/0.62  fof(f678,plain,(
% 2.00/0.62    spl6_54 | ~spl6_19 | ~spl6_44),
% 2.00/0.62    inference(avatar_split_clause,[],[f674,f540,f247,f676])).
% 2.00/0.62  fof(f540,plain,(
% 2.00/0.62    spl6_44 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 2.00/0.62  fof(f674,plain,(
% 2.00/0.62    ( ! [X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,k1_xboole_0)) ) | (~spl6_19 | ~spl6_44)),
% 2.00/0.62    inference(forward_demodulation,[],[f507,f542])).
% 2.00/0.62  fof(f542,plain,(
% 2.00/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_44),
% 2.00/0.62    inference(avatar_component_clause,[],[f540])).
% 2.00/0.62  fof(f507,plain,(
% 2.00/0.62    ( ! [X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X1,k1_xboole_0)) ) | ~spl6_19),
% 2.00/0.62    inference(resolution,[],[f228,f248])).
% 2.00/0.62  fof(f228,plain,(
% 2.00/0.62    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relat_1(X3) = k1_relset_1(k1_xboole_0,X2,X3)) )),
% 2.00/0.62    inference(superposition,[],[f78,f92])).
% 2.00/0.62  fof(f553,plain,(
% 2.00/0.62    spl6_45 | ~spl6_42),
% 2.00/0.62    inference(avatar_split_clause,[],[f524,f516,f550])).
% 2.00/0.62  fof(f516,plain,(
% 2.00/0.62    spl6_42 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 2.00/0.62  fof(f524,plain,(
% 2.00/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_42),
% 2.00/0.62    inference(superposition,[],[f59,f518])).
% 2.00/0.62  fof(f518,plain,(
% 2.00/0.62    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl6_42),
% 2.00/0.62    inference(avatar_component_clause,[],[f516])).
% 2.00/0.62  fof(f59,plain,(
% 2.00/0.62    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.00/0.62    inference(cnf_transformation,[],[f13])).
% 2.00/0.62  fof(f13,axiom,(
% 2.00/0.62    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.00/0.62  fof(f543,plain,(
% 2.00/0.62    spl6_44 | ~spl6_42),
% 2.00/0.62    inference(avatar_split_clause,[],[f523,f516,f540])).
% 2.00/0.62  fof(f523,plain,(
% 2.00/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_42),
% 2.00/0.62    inference(superposition,[],[f58,f518])).
% 2.00/0.62  fof(f58,plain,(
% 2.00/0.62    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.00/0.62    inference(cnf_transformation,[],[f13])).
% 2.00/0.62  fof(f519,plain,(
% 2.00/0.62    spl6_42),
% 2.00/0.62    inference(avatar_split_clause,[],[f489,f516])).
% 2.00/0.62  fof(f489,plain,(
% 2.00/0.62    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.00/0.62    inference(equality_resolution,[],[f485])).
% 2.00/0.62  fof(f485,plain,(
% 2.00/0.62    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_relat_1(X0)) )),
% 2.00/0.62    inference(subsumption_resolution,[],[f163,f450])).
% 2.00/0.62  fof(f450,plain,(
% 2.00/0.62    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.00/0.62    inference(resolution,[],[f154,f57])).
% 2.00/0.62  fof(f57,plain,(
% 2.00/0.62    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f18])).
% 2.00/0.62  fof(f18,axiom,(
% 2.00/0.62    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 2.00/0.62  fof(f154,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 2.00/0.62    inference(resolution,[],[f62,f64])).
% 2.00/0.62  fof(f64,plain,(
% 2.00/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f10])).
% 2.00/0.62  fof(f10,axiom,(
% 2.00/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.00/0.62  fof(f62,plain,(
% 2.00/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f26])).
% 2.00/0.62  fof(f26,plain,(
% 2.00/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.00/0.62    inference(ennf_transformation,[],[f8])).
% 2.00/0.62  fof(f8,axiom,(
% 2.00/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.00/0.62  fof(f163,plain,(
% 2.00/0.62    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_relat_1(X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.00/0.62    inference(superposition,[],[f60,f58])).
% 2.00/0.62  fof(f384,plain,(
% 2.00/0.62    spl6_31 | ~spl6_4 | ~spl6_5),
% 2.00/0.62    inference(avatar_split_clause,[],[f369,f124,f119,f381])).
% 2.00/0.62  fof(f124,plain,(
% 2.00/0.62    spl6_5 <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.00/0.62  fof(f369,plain,(
% 2.00/0.62    r1_tarski(k2_relat_1(sK3),sK2) | (~spl6_4 | ~spl6_5)),
% 2.00/0.62    inference(backward_demodulation,[],[f126,f230])).
% 2.00/0.62  fof(f230,plain,(
% 2.00/0.62    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl6_4),
% 2.00/0.62    inference(resolution,[],[f79,f121])).
% 2.00/0.62  fof(f79,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.00/0.62    inference(cnf_transformation,[],[f34])).
% 2.00/0.62  fof(f34,plain,(
% 2.00/0.62    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.00/0.62    inference(ennf_transformation,[],[f16])).
% 2.00/0.62  fof(f16,axiom,(
% 2.00/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.00/0.62  fof(f126,plain,(
% 2.00/0.62    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) | ~spl6_5),
% 2.00/0.62    inference(avatar_component_clause,[],[f124])).
% 2.00/0.62  fof(f342,plain,(
% 2.00/0.62    ~spl6_27 | ~spl6_7 | spl6_15),
% 2.00/0.62    inference(avatar_split_clause,[],[f323,f213,f133,f339])).
% 2.00/0.62  fof(f323,plain,(
% 2.00/0.62    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl6_7 | spl6_15)),
% 2.00/0.62    inference(backward_demodulation,[],[f215,f135])).
% 2.00/0.62  fof(f313,plain,(
% 2.00/0.62    spl6_25 | ~spl6_4 | ~spl6_24),
% 2.00/0.62    inference(avatar_split_clause,[],[f307,f301,f119,f310])).
% 2.00/0.62  fof(f301,plain,(
% 2.00/0.62    spl6_24 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 2.00/0.62  fof(f307,plain,(
% 2.00/0.62    sK0 = k1_relat_1(sK3) | (~spl6_4 | ~spl6_24)),
% 2.00/0.62    inference(forward_demodulation,[],[f224,f303])).
% 2.00/0.62  fof(f303,plain,(
% 2.00/0.62    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_24),
% 2.00/0.62    inference(avatar_component_clause,[],[f301])).
% 2.00/0.62  fof(f224,plain,(
% 2.00/0.62    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl6_4),
% 2.00/0.62    inference(resolution,[],[f78,f121])).
% 2.00/0.62  fof(f304,plain,(
% 2.00/0.62    spl6_24 | ~spl6_2 | ~spl6_4 | spl6_6),
% 2.00/0.62    inference(avatar_split_clause,[],[f299,f129,f119,f106,f301])).
% 2.00/0.62  fof(f299,plain,(
% 2.00/0.62    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl6_2 | ~spl6_4 | spl6_6)),
% 2.00/0.62    inference(subsumption_resolution,[],[f298,f121])).
% 2.00/0.62  fof(f298,plain,(
% 2.00/0.62    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl6_2 | spl6_6)),
% 2.00/0.62    inference(subsumption_resolution,[],[f296,f131])).
% 2.00/0.62  fof(f131,plain,(
% 2.00/0.62    k1_xboole_0 != sK1 | spl6_6),
% 2.00/0.62    inference(avatar_component_clause,[],[f129])).
% 2.00/0.62  fof(f296,plain,(
% 2.00/0.62    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_2),
% 2.00/0.62    inference(resolution,[],[f82,f108])).
% 2.00/0.62  fof(f82,plain,(
% 2.00/0.62    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.00/0.62    inference(cnf_transformation,[],[f49])).
% 2.00/0.62  fof(f285,plain,(
% 2.00/0.62    ~spl6_4 | spl6_21),
% 2.00/0.62    inference(avatar_contradiction_clause,[],[f284])).
% 2.00/0.62  fof(f284,plain,(
% 2.00/0.62    $false | (~spl6_4 | spl6_21)),
% 2.00/0.62    inference(unit_resulting_resolution,[],[f64,f121,f277,f62])).
% 2.00/0.62  fof(f277,plain,(
% 2.00/0.62    ~v1_relat_1(sK3) | spl6_21),
% 2.00/0.62    inference(avatar_component_clause,[],[f275])).
% 2.00/0.62  fof(f255,plain,(
% 2.00/0.62    spl6_19),
% 2.00/0.62    inference(avatar_contradiction_clause,[],[f254])).
% 2.00/0.62  fof(f254,plain,(
% 2.00/0.62    $false | spl6_19),
% 2.00/0.62    inference(subsumption_resolution,[],[f252,f89])).
% 2.00/0.62  fof(f252,plain,(
% 2.00/0.62    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl6_19),
% 2.00/0.62    inference(resolution,[],[f249,f73])).
% 2.00/0.62  fof(f249,plain,(
% 2.00/0.62    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl6_19),
% 2.00/0.62    inference(avatar_component_clause,[],[f247])).
% 2.00/0.62  fof(f220,plain,(
% 2.00/0.62    ~spl6_15 | ~spl6_16 | ~spl6_1),
% 2.00/0.62    inference(avatar_split_clause,[],[f211,f101,f217,f213])).
% 2.00/0.62  fof(f101,plain,(
% 2.00/0.62    spl6_1 <=> v1_funct_1(sK3)),
% 2.00/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.00/0.62  fof(f211,plain,(
% 2.00/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~spl6_1),
% 2.00/0.62    inference(subsumption_resolution,[],[f55,f103])).
% 2.00/0.62  fof(f103,plain,(
% 2.00/0.62    v1_funct_1(sK3) | ~spl6_1),
% 2.00/0.62    inference(avatar_component_clause,[],[f101])).
% 2.00/0.62  fof(f55,plain,(
% 2.00/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.00/0.62    inference(cnf_transformation,[],[f40])).
% 2.00/0.62  fof(f40,plain,(
% 2.00/0.62    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.00/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f39])).
% 2.00/0.62  fof(f39,plain,(
% 2.00/0.62    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.00/0.62    introduced(choice_axiom,[])).
% 2.00/0.62  fof(f23,plain,(
% 2.00/0.62    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.00/0.62    inference(flattening,[],[f22])).
% 2.00/0.62  fof(f22,plain,(
% 2.00/0.62    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.00/0.62    inference(ennf_transformation,[],[f21])).
% 2.00/0.62  fof(f21,negated_conjecture,(
% 2.00/0.62    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.00/0.62    inference(negated_conjecture,[],[f20])).
% 2.00/0.62  fof(f20,conjecture,(
% 2.00/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.00/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 2.00/0.62  fof(f136,plain,(
% 2.00/0.62    ~spl6_6 | spl6_7),
% 2.00/0.62    inference(avatar_split_clause,[],[f54,f133,f129])).
% 2.00/0.62  fof(f54,plain,(
% 2.00/0.62    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.00/0.62    inference(cnf_transformation,[],[f40])).
% 2.00/0.62  fof(f127,plain,(
% 2.00/0.62    spl6_5),
% 2.00/0.62    inference(avatar_split_clause,[],[f53,f124])).
% 2.00/0.62  fof(f53,plain,(
% 2.00/0.62    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 2.00/0.62    inference(cnf_transformation,[],[f40])).
% 2.00/0.62  fof(f122,plain,(
% 2.00/0.62    spl6_4),
% 2.00/0.62    inference(avatar_split_clause,[],[f52,f119])).
% 2.00/0.62  fof(f52,plain,(
% 2.00/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.00/0.62    inference(cnf_transformation,[],[f40])).
% 2.00/0.62  fof(f109,plain,(
% 2.00/0.62    spl6_2),
% 2.00/0.62    inference(avatar_split_clause,[],[f51,f106])).
% 2.00/0.62  fof(f51,plain,(
% 2.00/0.62    v1_funct_2(sK3,sK0,sK1)),
% 2.00/0.62    inference(cnf_transformation,[],[f40])).
% 2.00/0.62  fof(f104,plain,(
% 2.00/0.62    spl6_1),
% 2.00/0.62    inference(avatar_split_clause,[],[f50,f101])).
% 2.00/0.62  fof(f50,plain,(
% 2.00/0.62    v1_funct_1(sK3)),
% 2.00/0.62    inference(cnf_transformation,[],[f40])).
% 2.00/0.62  % SZS output end Proof for theBenchmark
% 2.00/0.62  % (7294)------------------------------
% 2.00/0.62  % (7294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.62  % (7294)Termination reason: Refutation
% 2.00/0.62  
% 2.00/0.62  % (7294)Memory used [KB]: 7164
% 2.00/0.62  % (7294)Time elapsed: 0.184 s
% 2.00/0.62  % (7294)------------------------------
% 2.00/0.62  % (7294)------------------------------
% 2.00/0.62  % (7291)Success in time 0.257 s
%------------------------------------------------------------------------------
