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
% DateTime   : Thu Dec  3 13:08:14 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 365 expanded)
%              Number of leaves         :   39 ( 153 expanded)
%              Depth                    :   12
%              Number of atoms          :  772 (1484 expanded)
%              Number of equality atoms :   85 ( 135 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f446,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f97,f101,f105,f159,f163,f171,f179,f199,f203,f212,f224,f236,f242,f248,f257,f279,f296,f428,f444,f445])).

fof(f445,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5)
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f444,plain,
    ( spl6_47
    | spl6_3
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_34
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f440,f426,f294,f246,f240,f86,f78,f442])).

fof(f442,plain,
    ( spl6_47
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f78,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f86,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f240,plain,
    ( spl6_27
  <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f246,plain,
    ( spl6_28
  <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f294,plain,
    ( spl6_34
  <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f426,plain,
    ( spl6_45
  <=> k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f440,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | spl6_3
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_34
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f439,f427])).

fof(f427,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f426])).

fof(f439,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_3
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_34 ),
    inference(resolution,[],[f372,f87])).

fof(f87,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f372,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | spl6_3
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f371,f79])).

fof(f79,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f371,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f370,f247])).

fof(f247,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f246])).

fof(f370,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_27
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f358,f241])).

fof(f241,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f240])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
        | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_34 ),
    inference(resolution,[],[f295,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f295,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f294])).

fof(f428,plain,
    ( spl6_45
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f396,f255,f207,f201,f197,f103,f99,f95,f82,f74,f70,f426])).

fof(f70,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f74,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f82,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f95,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f99,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f103,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f197,plain,
    ( spl6_19
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f201,plain,
    ( spl6_20
  <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f207,plain,
    ( spl6_21
  <=> sK0 = k1_relset_1(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f255,plain,
    ( spl6_30
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k7_partfun1(X3,X2,k1_funct_1(X0,sK5))
        | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f396,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f395,f71])).

fof(f71,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f395,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK4)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f394,f100])).

fof(f100,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f394,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f393,f198])).

fof(f198,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f197])).

fof(f393,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_30 ),
    inference(superposition,[],[f286,f208])).

fof(f208,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f207])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k7_partfun1(X0,X1,k1_funct_1(sK3,sK5))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1) )
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_20
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f285,f96])).

fof(f96,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k7_partfun1(X0,X1,k1_funct_1(sK3,sK5))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_2
    | spl6_4
    | ~ spl6_9
    | ~ spl6_20
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f284,f104])).

fof(f104,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k7_partfun1(X0,X1,k1_funct_1(sK3,sK5))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_2
    | spl6_4
    | ~ spl6_20
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f283,f83])).

fof(f83,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f283,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k7_partfun1(X0,X1,k1_funct_1(sK3,sK5))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_2
    | ~ spl6_20
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f280,f75])).

fof(f75,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k7_partfun1(X0,X1,k1_funct_1(sK3,sK5))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(sK3,sK1,sK0) )
    | ~ spl6_20
    | ~ spl6_30 ),
    inference(superposition,[],[f256,f202])).

fof(f202,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f256,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k7_partfun1(X3,X2,k1_funct_1(X0,sK5))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f255])).

fof(f296,plain,
    ( spl6_34
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f250,f103,f99,f95,f74,f70,f294])).

fof(f250,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f249,f71])).

fof(f249,plain,
    ( ~ v1_funct_1(sK4)
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f153,f100])).

fof(f153,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | ~ v1_funct_1(X5)
        | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6))) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f152,f75])).

fof(f152,plain,
    ( ! [X6,X5] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6))) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f136,f96])).

fof(f136,plain,
    ( ! [X6,X5] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6))) )
    | ~ spl6_9 ),
    inference(resolution,[],[f104,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f279,plain,
    ( spl6_3
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl6_3
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f267,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f267,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_29 ),
    inference(superposition,[],[f79,f253])).

fof(f253,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl6_29
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f257,plain,
    ( spl6_29
    | spl6_30
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f93,f86,f255,f252])).

fof(f93,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | v1_xboole_0(X1)
        | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k7_partfun1(X3,X2,k1_funct_1(X0,sK5)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f87,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f248,plain,
    ( spl6_28
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f244,f103,f99,f95,f74,f70,f246])).

fof(f244,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f243,f71])).

fof(f243,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f151,f100])).

fof(f151,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
        | ~ v1_funct_1(X3)
        | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f150,f75])).

fof(f150,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
        | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f135,f96])).

fof(f135,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
        | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4) )
    | ~ spl6_9 ),
    inference(resolution,[],[f104,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f242,plain,
    ( spl6_27
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f238,f103,f99,f95,f74,f70,f240])).

fof(f238,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f237,f71])).

fof(f237,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f149,f100])).

fof(f149,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_funct_1(X1)
        | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1)) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f148,f75])).

fof(f148,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1)) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f134,f96])).

fof(f134,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1)) )
    | ~ spl6_9 ),
    inference(resolution,[],[f104,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f236,plain,
    ( spl6_26
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f232,f103,f95,f86,f78,f74,f234])).

fof(f234,plain,
    ( spl6_26
  <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f232,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f147,f87])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f146,f79])).

fof(f146,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f145,f96])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f133,f75])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_9 ),
    inference(resolution,[],[f104,f45])).

fof(f224,plain,
    ( spl6_10
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl6_10
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f217,f51])).

fof(f217,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_10
    | ~ spl6_22 ),
    inference(superposition,[],[f158,f211])).

fof(f211,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_22
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f158,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl6_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f212,plain,
    ( spl6_21
    | spl6_22
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f131,f99,f90,f70,f210,f207])).

fof(f90,plain,
    ( spl6_6
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f131,plain,
    ( k1_xboole_0 = sK2
    | sK0 = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f113,f124])).

fof(f124,plain,
    ( v1_funct_2(sK4,sK0,sK2)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f123,f91])).

fof(f91,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f123,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | v1_funct_2(sK4,sK0,sK2)
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f110,f71])).

fof(f110,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_partfun1(sK4,sK0)
    | v1_funct_2(sK4,sK0,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f100,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_funct_2)).

fof(f113,plain,
    ( k1_xboole_0 = sK2
    | sK0 = k1_relset_1(sK0,sK2,sK4)
    | ~ v1_funct_2(sK4,sK0,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f100,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f203,plain,
    ( spl6_20
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f141,f103,f201])).

fof(f141,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_9 ),
    inference(resolution,[],[f104,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f199,plain,
    ( spl6_19
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f183,f177,f169,f197])).

fof(f169,plain,
    ( spl6_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f177,plain,
    ( spl6_15
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f183,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_13
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f182,f170])).

fof(f170,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f182,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_15 ),
    inference(resolution,[],[f178,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f178,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,
    ( spl6_15
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f142,f103,f177])).

fof(f142,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f104,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f171,plain,
    ( spl6_13
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f155,f103,f169])).

fof(f155,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f143,f62])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f143,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3)
    | ~ spl6_9 ),
    inference(resolution,[],[f104,f63])).

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f163,plain,(
    ~ spl6_11 ),
    inference(avatar_split_clause,[],[f36,f161])).

fof(f161,plain,
    ( spl6_11
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f36,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

fof(f159,plain,
    ( ~ spl6_10
    | spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f130,f99,f90,f82,f157])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f129,f91])).

fof(f129,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_partfun1(sK4,sK0)
    | spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f111,f83])).

fof(f111,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_partfun1(sK4,sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f100,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f105,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f41,f103])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f38,f99])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f40,f95])).

fof(f40,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f35,f90])).

fof(f35,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f34,f86])).

fof(f34,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f43,f82])).

fof(f43,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f42,f78])).

fof(f42,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f37,f70])).

fof(f37,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (21825)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.43  % (21825)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f446,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f97,f101,f105,f159,f163,f171,f179,f199,f203,f212,f224,f236,f242,f248,f257,f279,f296,f428,f444,f445])).
% 0.19/0.43  fof(f445,plain,(
% 0.19/0.43    k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.19/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.43  fof(f444,plain,(
% 0.19/0.43    spl6_47 | spl6_3 | ~spl6_5 | ~spl6_27 | ~spl6_28 | ~spl6_34 | ~spl6_45),
% 0.19/0.43    inference(avatar_split_clause,[],[f440,f426,f294,f246,f240,f86,f78,f442])).
% 0.19/0.43  fof(f442,plain,(
% 0.19/0.43    spl6_47 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.19/0.43  fof(f78,plain,(
% 0.19/0.43    spl6_3 <=> v1_xboole_0(sK1)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.43  fof(f86,plain,(
% 0.19/0.43    spl6_5 <=> m1_subset_1(sK5,sK1)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.19/0.43  fof(f240,plain,(
% 0.19/0.43    spl6_27 <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.19/0.43  fof(f246,plain,(
% 0.19/0.43    spl6_28 <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.19/0.43  fof(f294,plain,(
% 0.19/0.43    spl6_34 <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.19/0.43  fof(f426,plain,(
% 0.19/0.43    spl6_45 <=> k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.19/0.43  fof(f440,plain,(
% 0.19/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (spl6_3 | ~spl6_5 | ~spl6_27 | ~spl6_28 | ~spl6_34 | ~spl6_45)),
% 0.19/0.43    inference(forward_demodulation,[],[f439,f427])).
% 0.19/0.43  fof(f427,plain,(
% 0.19/0.43    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~spl6_45),
% 0.19/0.43    inference(avatar_component_clause,[],[f426])).
% 0.19/0.43  fof(f439,plain,(
% 0.19/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (spl6_3 | ~spl6_5 | ~spl6_27 | ~spl6_28 | ~spl6_34)),
% 0.19/0.43    inference(resolution,[],[f372,f87])).
% 0.19/0.43  fof(f87,plain,(
% 0.19/0.43    m1_subset_1(sK5,sK1) | ~spl6_5),
% 0.19/0.43    inference(avatar_component_clause,[],[f86])).
% 0.19/0.43  fof(f372,plain,(
% 0.19/0.43    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (spl6_3 | ~spl6_27 | ~spl6_28 | ~spl6_34)),
% 0.19/0.43    inference(subsumption_resolution,[],[f371,f79])).
% 0.19/0.43  fof(f79,plain,(
% 0.19/0.43    ~v1_xboole_0(sK1) | spl6_3),
% 0.19/0.43    inference(avatar_component_clause,[],[f78])).
% 0.19/0.43  fof(f371,plain,(
% 0.19/0.43    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (~spl6_27 | ~spl6_28 | ~spl6_34)),
% 0.19/0.43    inference(subsumption_resolution,[],[f370,f247])).
% 0.19/0.43  fof(f247,plain,(
% 0.19/0.43    v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~spl6_28),
% 0.19/0.43    inference(avatar_component_clause,[],[f246])).
% 0.19/0.43  fof(f370,plain,(
% 0.19/0.43    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (~spl6_27 | ~spl6_34)),
% 0.19/0.43    inference(subsumption_resolution,[],[f358,f241])).
% 0.19/0.43  fof(f241,plain,(
% 0.19/0.43    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~spl6_27),
% 0.19/0.43    inference(avatar_component_clause,[],[f240])).
% 0.19/0.43  fof(f358,plain,(
% 0.19/0.43    ( ! [X0] : (~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | ~spl6_34),
% 0.19/0.43    inference(resolution,[],[f295,f45])).
% 0.19/0.43  fof(f45,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f21])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.19/0.43    inference(flattening,[],[f20])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.19/0.43    inference(ennf_transformation,[],[f10])).
% 0.19/0.43  fof(f10,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.19/0.43  fof(f295,plain,(
% 0.19/0.43    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_34),
% 0.19/0.43    inference(avatar_component_clause,[],[f294])).
% 0.19/0.43  fof(f428,plain,(
% 0.19/0.43    spl6_45 | ~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_19 | ~spl6_20 | ~spl6_21 | ~spl6_30),
% 0.19/0.43    inference(avatar_split_clause,[],[f396,f255,f207,f201,f197,f103,f99,f95,f82,f74,f70,f426])).
% 0.19/0.43  fof(f70,plain,(
% 0.19/0.43    spl6_1 <=> v1_funct_1(sK4)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.43  fof(f74,plain,(
% 0.19/0.43    spl6_2 <=> v1_funct_1(sK3)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.43  fof(f82,plain,(
% 0.19/0.43    spl6_4 <=> v1_xboole_0(sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.19/0.43  fof(f95,plain,(
% 0.19/0.43    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.19/0.43  fof(f99,plain,(
% 0.19/0.43    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.19/0.43  fof(f103,plain,(
% 0.19/0.43    spl6_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.19/0.43  fof(f197,plain,(
% 0.19/0.43    spl6_19 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.19/0.43  fof(f201,plain,(
% 0.19/0.43    spl6_20 <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.19/0.43  fof(f207,plain,(
% 0.19/0.43    spl6_21 <=> sK0 = k1_relset_1(sK0,sK2,sK4)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.19/0.43  fof(f255,plain,(
% 0.19/0.43    spl6_30 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X0) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k7_partfun1(X3,X2,k1_funct_1(X0,sK5)) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.19/0.43  fof(f396,plain,(
% 0.19/0.43    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_19 | ~spl6_20 | ~spl6_21 | ~spl6_30)),
% 0.19/0.43    inference(subsumption_resolution,[],[f395,f71])).
% 0.19/0.43  fof(f71,plain,(
% 0.19/0.43    v1_funct_1(sK4) | ~spl6_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f70])).
% 0.19/0.43  fof(f395,plain,(
% 0.19/0.43    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK4) | (~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_19 | ~spl6_20 | ~spl6_21 | ~spl6_30)),
% 0.19/0.43    inference(subsumption_resolution,[],[f394,f100])).
% 0.19/0.43  fof(f100,plain,(
% 0.19/0.43    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_8),
% 0.19/0.43    inference(avatar_component_clause,[],[f99])).
% 0.19/0.43  fof(f394,plain,(
% 0.19/0.43    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | (~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_9 | ~spl6_19 | ~spl6_20 | ~spl6_21 | ~spl6_30)),
% 0.19/0.43    inference(subsumption_resolution,[],[f393,f198])).
% 0.19/0.43  fof(f198,plain,(
% 0.19/0.43    r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_19),
% 0.19/0.43    inference(avatar_component_clause,[],[f197])).
% 0.19/0.43  fof(f393,plain,(
% 0.19/0.43    ~r1_tarski(k2_relat_1(sK3),sK0) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | (~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_9 | ~spl6_20 | ~spl6_21 | ~spl6_30)),
% 0.19/0.43    inference(superposition,[],[f286,f208])).
% 0.19/0.43  fof(f208,plain,(
% 0.19/0.43    sK0 = k1_relset_1(sK0,sK2,sK4) | ~spl6_21),
% 0.19/0.43    inference(avatar_component_clause,[],[f207])).
% 0.19/0.43  fof(f286,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k7_partfun1(X0,X1,k1_funct_1(sK3,sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1)) ) | (~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_9 | ~spl6_20 | ~spl6_30)),
% 0.19/0.43    inference(subsumption_resolution,[],[f285,f96])).
% 0.19/0.43  fof(f96,plain,(
% 0.19/0.43    v1_funct_2(sK3,sK1,sK0) | ~spl6_7),
% 0.19/0.43    inference(avatar_component_clause,[],[f95])).
% 0.19/0.43  fof(f285,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k7_partfun1(X0,X1,k1_funct_1(sK3,sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_2 | spl6_4 | ~spl6_9 | ~spl6_20 | ~spl6_30)),
% 0.19/0.43    inference(subsumption_resolution,[],[f284,f104])).
% 0.19/0.43  fof(f104,plain,(
% 0.19/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_9),
% 0.19/0.43    inference(avatar_component_clause,[],[f103])).
% 0.19/0.43  fof(f284,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k7_partfun1(X0,X1,k1_funct_1(sK3,sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_2 | spl6_4 | ~spl6_20 | ~spl6_30)),
% 0.19/0.43    inference(subsumption_resolution,[],[f283,f83])).
% 0.19/0.43  fof(f83,plain,(
% 0.19/0.43    ~v1_xboole_0(sK0) | spl6_4),
% 0.19/0.43    inference(avatar_component_clause,[],[f82])).
% 0.19/0.43  fof(f283,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k7_partfun1(X0,X1,k1_funct_1(sK3,sK5)) | v1_xboole_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_2 | ~spl6_20 | ~spl6_30)),
% 0.19/0.43    inference(subsumption_resolution,[],[f280,f75])).
% 0.19/0.43  fof(f75,plain,(
% 0.19/0.43    v1_funct_1(sK3) | ~spl6_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f74])).
% 0.19/0.43  fof(f280,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK0,X0,X1)) | k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),sK5) = k7_partfun1(X0,X1,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0)) ) | (~spl6_20 | ~spl6_30)),
% 0.19/0.43    inference(superposition,[],[f256,f202])).
% 0.19/0.43  fof(f202,plain,(
% 0.19/0.43    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_20),
% 0.19/0.43    inference(avatar_component_clause,[],[f201])).
% 0.19/0.43  fof(f256,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k7_partfun1(X3,X2,k1_funct_1(X0,sK5)) | ~v1_funct_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl6_30),
% 0.19/0.43    inference(avatar_component_clause,[],[f255])).
% 0.19/0.43  fof(f296,plain,(
% 0.19/0.43    spl6_34 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.19/0.43    inference(avatar_split_clause,[],[f250,f103,f99,f95,f74,f70,f294])).
% 0.19/0.43  fof(f250,plain,(
% 0.19/0.43    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f249,f71])).
% 0.19/0.43  fof(f249,plain,(
% 0.19/0.43    ~v1_funct_1(sK4) | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.19/0.43    inference(resolution,[],[f153,f100])).
% 0.19/0.43  fof(f153,plain,(
% 0.19/0.43    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | ~v1_funct_1(X5) | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6)))) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f152,f75])).
% 0.19/0.43  fof(f152,plain,(
% 0.19/0.43    ( ! [X6,X5] : (~v1_funct_1(sK3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6)))) ) | (~spl6_7 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f136,f96])).
% 0.19/0.43  fof(f136,plain,(
% 0.19/0.43    ( ! [X6,X5] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | m1_subset_1(k8_funct_2(sK1,sK0,X6,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(sK1,X6)))) ) | ~spl6_9),
% 0.19/0.43    inference(resolution,[],[f104,f48])).
% 0.19/0.43  fof(f48,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f23])).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.43    inference(flattening,[],[f22])).
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.43    inference(ennf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 0.19/0.43  fof(f279,plain,(
% 0.19/0.43    spl6_3 | ~spl6_29),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f278])).
% 0.19/0.43  fof(f278,plain,(
% 0.19/0.43    $false | (spl6_3 | ~spl6_29)),
% 0.19/0.43    inference(subsumption_resolution,[],[f267,f51])).
% 0.19/0.43  fof(f51,plain,(
% 0.19/0.43    v1_xboole_0(k1_xboole_0)),
% 0.19/0.43    inference(cnf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    v1_xboole_0(k1_xboole_0)),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.43  fof(f267,plain,(
% 0.19/0.43    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_29)),
% 0.19/0.43    inference(superposition,[],[f79,f253])).
% 0.19/0.43  fof(f253,plain,(
% 0.19/0.43    k1_xboole_0 = sK1 | ~spl6_29),
% 0.19/0.43    inference(avatar_component_clause,[],[f252])).
% 0.19/0.43  fof(f252,plain,(
% 0.19/0.43    spl6_29 <=> k1_xboole_0 = sK1),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.19/0.43  fof(f257,plain,(
% 0.19/0.43    spl6_29 | spl6_30 | ~spl6_5),
% 0.19/0.43    inference(avatar_split_clause,[],[f93,f86,f255,f252])).
% 0.19/0.43  fof(f93,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k7_partfun1(X3,X2,k1_funct_1(X0,sK5))) ) | ~spl6_5),
% 0.19/0.43    inference(resolution,[],[f87,f44])).
% 0.19/0.43  fof(f44,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f19])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.19/0.43    inference(flattening,[],[f18])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.19/0.43    inference(ennf_transformation,[],[f12])).
% 0.19/0.43  fof(f12,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.19/0.43  fof(f248,plain,(
% 0.19/0.43    spl6_28 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.19/0.43    inference(avatar_split_clause,[],[f244,f103,f99,f95,f74,f70,f246])).
% 0.19/0.43  fof(f244,plain,(
% 0.19/0.43    v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f243,f71])).
% 0.19/0.43  fof(f243,plain,(
% 0.19/0.43    ~v1_funct_1(sK4) | v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.19/0.43    inference(resolution,[],[f151,f100])).
% 0.19/0.43  fof(f151,plain,(
% 0.19/0.43    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~v1_funct_1(X3) | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4)) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f150,f75])).
% 0.19/0.43  fof(f150,plain,(
% 0.19/0.43    ( ! [X4,X3] : (~v1_funct_1(sK3) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4)) ) | (~spl6_7 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f135,f96])).
% 0.19/0.43  fof(f135,plain,(
% 0.19/0.43    ( ! [X4,X3] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | v1_funct_2(k8_funct_2(sK1,sK0,X4,sK3,X3),sK1,X4)) ) | ~spl6_9),
% 0.19/0.43    inference(resolution,[],[f104,f47])).
% 0.19/0.43  fof(f47,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f23])).
% 0.19/0.43  fof(f242,plain,(
% 0.19/0.43    spl6_27 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.19/0.43    inference(avatar_split_clause,[],[f238,f103,f99,f95,f74,f70,f240])).
% 0.19/0.43  fof(f238,plain,(
% 0.19/0.43    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f237,f71])).
% 0.19/0.43  fof(f237,plain,(
% 0.19/0.43    ~v1_funct_1(sK4) | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.19/0.43    inference(resolution,[],[f149,f100])).
% 0.19/0.43  fof(f149,plain,(
% 0.19/0.43    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | ~v1_funct_1(X1) | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1))) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f148,f75])).
% 0.19/0.43  fof(f148,plain,(
% 0.19/0.43    ( ! [X2,X1] : (~v1_funct_1(sK3) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1))) ) | (~spl6_7 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f134,f96])).
% 0.19/0.43  fof(f134,plain,(
% 0.19/0.43    ( ! [X2,X1] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) | v1_funct_1(k8_funct_2(sK1,sK0,X2,sK3,X1))) ) | ~spl6_9),
% 0.19/0.43    inference(resolution,[],[f104,f46])).
% 0.19/0.43  fof(f46,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f23])).
% 0.19/0.43  fof(f236,plain,(
% 0.19/0.43    spl6_26 | ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9),
% 0.19/0.43    inference(avatar_split_clause,[],[f232,f103,f95,f86,f78,f74,f234])).
% 0.19/0.43  fof(f234,plain,(
% 0.19/0.43    spl6_26 <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.19/0.43  fof(f232,plain,(
% 0.19/0.43    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9)),
% 0.19/0.43    inference(resolution,[],[f147,f87])).
% 0.19/0.43  fof(f147,plain,(
% 0.19/0.43    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl6_2 | spl6_3 | ~spl6_7 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f146,f79])).
% 0.19/0.43  fof(f146,plain,(
% 0.19/0.43    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f145,f96])).
% 0.19/0.43  fof(f145,plain,(
% 0.19/0.43    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl6_2 | ~spl6_9)),
% 0.19/0.43    inference(subsumption_resolution,[],[f133,f75])).
% 0.19/0.43  fof(f133,plain,(
% 0.19/0.43    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | ~spl6_9),
% 0.19/0.43    inference(resolution,[],[f104,f45])).
% 0.19/0.43  fof(f224,plain,(
% 0.19/0.43    spl6_10 | ~spl6_22),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f223])).
% 0.19/0.43  fof(f223,plain,(
% 0.19/0.43    $false | (spl6_10 | ~spl6_22)),
% 0.19/0.43    inference(subsumption_resolution,[],[f217,f51])).
% 0.19/0.43  fof(f217,plain,(
% 0.19/0.43    ~v1_xboole_0(k1_xboole_0) | (spl6_10 | ~spl6_22)),
% 0.19/0.43    inference(superposition,[],[f158,f211])).
% 0.19/0.43  fof(f211,plain,(
% 0.19/0.43    k1_xboole_0 = sK2 | ~spl6_22),
% 0.19/0.43    inference(avatar_component_clause,[],[f210])).
% 0.19/0.43  fof(f210,plain,(
% 0.19/0.43    spl6_22 <=> k1_xboole_0 = sK2),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.19/0.43  fof(f158,plain,(
% 0.19/0.43    ~v1_xboole_0(sK2) | spl6_10),
% 0.19/0.43    inference(avatar_component_clause,[],[f157])).
% 0.19/0.43  fof(f157,plain,(
% 0.19/0.43    spl6_10 <=> v1_xboole_0(sK2)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.19/0.43  fof(f212,plain,(
% 0.19/0.43    spl6_21 | spl6_22 | ~spl6_1 | ~spl6_6 | ~spl6_8),
% 0.19/0.43    inference(avatar_split_clause,[],[f131,f99,f90,f70,f210,f207])).
% 0.19/0.43  fof(f90,plain,(
% 0.19/0.43    spl6_6 <=> v1_partfun1(sK4,sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.19/0.43  fof(f131,plain,(
% 0.19/0.43    k1_xboole_0 = sK2 | sK0 = k1_relset_1(sK0,sK2,sK4) | (~spl6_1 | ~spl6_6 | ~spl6_8)),
% 0.19/0.43    inference(subsumption_resolution,[],[f113,f124])).
% 0.19/0.43  fof(f124,plain,(
% 0.19/0.43    v1_funct_2(sK4,sK0,sK2) | (~spl6_1 | ~spl6_6 | ~spl6_8)),
% 0.19/0.43    inference(subsumption_resolution,[],[f123,f91])).
% 0.19/0.43  fof(f91,plain,(
% 0.19/0.43    v1_partfun1(sK4,sK0) | ~spl6_6),
% 0.19/0.43    inference(avatar_component_clause,[],[f90])).
% 0.19/0.43  fof(f123,plain,(
% 0.19/0.43    ~v1_partfun1(sK4,sK0) | v1_funct_2(sK4,sK0,sK2) | (~spl6_1 | ~spl6_8)),
% 0.19/0.43    inference(subsumption_resolution,[],[f110,f71])).
% 0.19/0.43  fof(f110,plain,(
% 0.19/0.43    ~v1_funct_1(sK4) | ~v1_partfun1(sK4,sK0) | v1_funct_2(sK4,sK0,sK2) | ~spl6_8),
% 0.19/0.43    inference(resolution,[],[f100,f49])).
% 0.19/0.43  fof(f49,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f25])).
% 0.19/0.43  fof(f25,plain,(
% 0.19/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.19/0.43    inference(flattening,[],[f24])).
% 0.19/0.43  fof(f24,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.19/0.43    inference(ennf_transformation,[],[f11])).
% 0.19/0.43  fof(f11,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_funct_2)).
% 0.19/0.43  fof(f113,plain,(
% 0.19/0.43    k1_xboole_0 = sK2 | sK0 = k1_relset_1(sK0,sK2,sK4) | ~v1_funct_2(sK4,sK0,sK2) | ~spl6_8),
% 0.19/0.43    inference(resolution,[],[f100,f57])).
% 0.19/0.43  fof(f57,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f29])).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(flattening,[],[f28])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f8])).
% 0.19/0.44  fof(f8,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.44  fof(f203,plain,(
% 0.19/0.44    spl6_20 | ~spl6_9),
% 0.19/0.44    inference(avatar_split_clause,[],[f141,f103,f201])).
% 0.19/0.44  fof(f141,plain,(
% 0.19/0.44    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_9),
% 0.19/0.44    inference(resolution,[],[f104,f60])).
% 0.19/0.44  fof(f60,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f31])).
% 0.19/0.44  fof(f31,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.44  fof(f199,plain,(
% 0.19/0.44    spl6_19 | ~spl6_13 | ~spl6_15),
% 0.19/0.44    inference(avatar_split_clause,[],[f183,f177,f169,f197])).
% 0.19/0.44  fof(f169,plain,(
% 0.19/0.44    spl6_13 <=> v1_relat_1(sK3)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.19/0.44  fof(f177,plain,(
% 0.19/0.44    spl6_15 <=> v5_relat_1(sK3,sK0)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.19/0.44  fof(f183,plain,(
% 0.19/0.44    r1_tarski(k2_relat_1(sK3),sK0) | (~spl6_13 | ~spl6_15)),
% 0.19/0.44    inference(subsumption_resolution,[],[f182,f170])).
% 0.19/0.44  fof(f170,plain,(
% 0.19/0.44    v1_relat_1(sK3) | ~spl6_13),
% 0.19/0.44    inference(avatar_component_clause,[],[f169])).
% 0.19/0.44  fof(f182,plain,(
% 0.19/0.44    r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | ~spl6_15),
% 0.19/0.44    inference(resolution,[],[f178,f59])).
% 0.19/0.44  fof(f59,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f30])).
% 0.19/0.44  fof(f30,plain,(
% 0.19/0.44    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.44  fof(f178,plain,(
% 0.19/0.44    v5_relat_1(sK3,sK0) | ~spl6_15),
% 0.19/0.44    inference(avatar_component_clause,[],[f177])).
% 0.19/0.44  fof(f179,plain,(
% 0.19/0.44    spl6_15 | ~spl6_9),
% 0.19/0.44    inference(avatar_split_clause,[],[f142,f103,f177])).
% 0.19/0.44  fof(f142,plain,(
% 0.19/0.44    v5_relat_1(sK3,sK0) | ~spl6_9),
% 0.19/0.44    inference(resolution,[],[f104,f61])).
% 0.19/0.44  fof(f61,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f32])).
% 0.19/0.44  fof(f32,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.44    inference(ennf_transformation,[],[f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.19/0.44    inference(pure_predicate_removal,[],[f5])).
% 0.19/0.44  fof(f5,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.44  fof(f171,plain,(
% 0.19/0.44    spl6_13 | ~spl6_9),
% 0.19/0.44    inference(avatar_split_clause,[],[f155,f103,f169])).
% 0.19/0.44  fof(f155,plain,(
% 0.19/0.44    v1_relat_1(sK3) | ~spl6_9),
% 0.19/0.44    inference(subsumption_resolution,[],[f143,f62])).
% 0.19/0.44  fof(f62,plain,(
% 0.19/0.44    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.44  fof(f143,plain,(
% 0.19/0.44    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3) | ~spl6_9),
% 0.19/0.44    inference(resolution,[],[f104,f63])).
% 0.19/0.44  fof(f63,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f33])).
% 0.19/0.44  fof(f33,plain,(
% 0.19/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.44  fof(f163,plain,(
% 0.19/0.44    ~spl6_11),
% 0.19/0.44    inference(avatar_split_clause,[],[f36,f161])).
% 0.19/0.44  fof(f161,plain,(
% 0.19/0.44    spl6_11 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.44    inference(flattening,[],[f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.44    inference(ennf_transformation,[],[f14])).
% 0.19/0.44  fof(f14,negated_conjecture,(
% 0.19/0.44    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.19/0.44    inference(negated_conjecture,[],[f13])).
% 0.19/0.44  fof(f13,conjecture,(
% 0.19/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).
% 0.19/0.44  fof(f159,plain,(
% 0.19/0.44    ~spl6_10 | spl6_4 | ~spl6_6 | ~spl6_8),
% 0.19/0.44    inference(avatar_split_clause,[],[f130,f99,f90,f82,f157])).
% 0.19/0.44  fof(f130,plain,(
% 0.19/0.44    ~v1_xboole_0(sK2) | (spl6_4 | ~spl6_6 | ~spl6_8)),
% 0.19/0.44    inference(subsumption_resolution,[],[f129,f91])).
% 0.19/0.44  fof(f129,plain,(
% 0.19/0.44    ~v1_xboole_0(sK2) | ~v1_partfun1(sK4,sK0) | (spl6_4 | ~spl6_8)),
% 0.19/0.44    inference(subsumption_resolution,[],[f111,f83])).
% 0.19/0.44  fof(f111,plain,(
% 0.19/0.44    ~v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~v1_partfun1(sK4,sK0) | ~spl6_8),
% 0.19/0.44    inference(resolution,[],[f100,f50])).
% 0.19/0.44  fof(f50,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_partfun1(X2,X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f27])).
% 0.19/0.44  fof(f27,plain,(
% 0.19/0.44    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.19/0.44    inference(flattening,[],[f26])).
% 0.19/0.44  fof(f26,plain,(
% 0.19/0.44    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f7])).
% 0.19/0.44  fof(f7,axiom,(
% 0.19/0.44    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.19/0.44  fof(f105,plain,(
% 0.19/0.44    spl6_9),
% 0.19/0.44    inference(avatar_split_clause,[],[f41,f103])).
% 0.19/0.44  fof(f41,plain,(
% 0.19/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f101,plain,(
% 0.19/0.44    spl6_8),
% 0.19/0.44    inference(avatar_split_clause,[],[f38,f99])).
% 0.19/0.44  fof(f38,plain,(
% 0.19/0.44    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f97,plain,(
% 0.19/0.44    spl6_7),
% 0.19/0.44    inference(avatar_split_clause,[],[f40,f95])).
% 0.19/0.44  fof(f40,plain,(
% 0.19/0.44    v1_funct_2(sK3,sK1,sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f92,plain,(
% 0.19/0.44    spl6_6),
% 0.19/0.44    inference(avatar_split_clause,[],[f35,f90])).
% 0.19/0.44  fof(f35,plain,(
% 0.19/0.44    v1_partfun1(sK4,sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f88,plain,(
% 0.19/0.44    spl6_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f34,f86])).
% 0.19/0.44  fof(f34,plain,(
% 0.19/0.44    m1_subset_1(sK5,sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f84,plain,(
% 0.19/0.44    ~spl6_4),
% 0.19/0.44    inference(avatar_split_clause,[],[f43,f82])).
% 0.19/0.44  fof(f43,plain,(
% 0.19/0.44    ~v1_xboole_0(sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f80,plain,(
% 0.19/0.44    ~spl6_3),
% 0.19/0.44    inference(avatar_split_clause,[],[f42,f78])).
% 0.19/0.44  fof(f42,plain,(
% 0.19/0.44    ~v1_xboole_0(sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f76,plain,(
% 0.19/0.44    spl6_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f39,f74])).
% 0.19/0.44  fof(f39,plain,(
% 0.19/0.44    v1_funct_1(sK3)),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  fof(f72,plain,(
% 0.19/0.44    spl6_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f37,f70])).
% 0.19/0.44  fof(f37,plain,(
% 0.19/0.44    v1_funct_1(sK4)),
% 0.19/0.44    inference(cnf_transformation,[],[f17])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (21825)------------------------------
% 0.19/0.44  % (21825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (21825)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (21825)Memory used [KB]: 6524
% 0.19/0.44  % (21825)Time elapsed: 0.037 s
% 0.19/0.44  % (21825)------------------------------
% 0.19/0.44  % (21825)------------------------------
% 0.19/0.44  % (21830)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.44  % (21824)Success in time 0.086 s
%------------------------------------------------------------------------------
