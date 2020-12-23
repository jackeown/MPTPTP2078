%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1034+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 169 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  345 ( 707 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f42,f47,f52,f57,f62,f72,f78,f88,f93,f98,f103,f110,f119])).

fof(f119,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_12
    | spl3_13
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_12
    | spl3_13
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f117,f22])).

fof(f22,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f117,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_12
    | spl3_13
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f116,f32])).

fof(f32,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_3
  <=> r1_partfun1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f116,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | spl3_13
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f115,f102])).

fof(f102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | spl3_13
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f114,f87])).

fof(f87,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_11
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f114,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_12
    | spl3_13
    | ~ spl3_15 ),
    inference(resolution,[],[f113,f97])).

fof(f97,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_13
  <=> r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f113,plain,
    ( ! [X0] :
        ( r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,X0)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ v1_funct_1(X0) )
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f111,f92])).

fof(f92,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_12
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(sK1,X0)
        | r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,X0) )
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(resolution,[],[f109,f37])).

fof(f37,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
        | ~ v1_funct_2(sK1,k1_xboole_0,X3)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,k1_xboole_0,X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
        | ~ r1_partfun1(sK1,X4)
        | r2_relset_1(k1_xboole_0,X3,sK1,X4) )
    | ~ spl3_2 ),
    inference(resolution,[],[f27,f18])).

fof(f18,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_partfun1(X2,X3)
      | r2_relset_1(k1_xboole_0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 != X0
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

% (16952)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f27,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f109,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f110,plain,
    ( spl3_15
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f83,f66,f59,f107])).

fof(f59,plain,
    ( spl3_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f66,plain,
    ( spl3_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(superposition,[],[f61,f68])).

fof(f68,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f103,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f82,f66,f54,f100])).

fof(f54,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f82,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(superposition,[],[f56,f68])).

fof(f56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f98,plain,
    ( ~ spl3_13
    | spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f81,f66,f49,f95])).

fof(f49,plain,
    ( spl3_6
  <=> r2_relset_1(sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f81,plain,
    ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK1,sK2)
    | spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f51,f68])).

fof(f51,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f93,plain,
    ( spl3_12
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f80,f66,f44,f90])).

fof(f44,plain,
    ( spl3_5
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f80,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f46,f68])).

fof(f46,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f88,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f79,f66,f39,f85])).

fof(f39,plain,
    ( spl3_4
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f79,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f41,f68])).

fof(f41,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f78,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f76,f41])).

fof(f76,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ spl3_1
    | ~ spl3_3
    | spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f75,f56])).

fof(f75,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ spl3_1
    | ~ spl3_3
    | spl3_6
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f74,f32])).

fof(f74,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ spl3_1
    | spl3_6
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f73,f22])).

fof(f73,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_partfun1(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f71,f51])).

fof(f71,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,sK0,sK1,X0)
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | r2_relset_1(sK0,sK0,sK1,X0)
        | ~ r1_partfun1(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f72,plain,
    ( spl3_9
    | spl3_10
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f64,f59,f44,f25,f70,f66])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X0)
        | k1_xboole_0 = sK0
        | r2_relset_1(sK0,sK0,sK1,X0) )
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f63,f46])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK1,sK0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X0)
        | k1_xboole_0 = sK0
        | r2_relset_1(sK0,sK0,sK1,X0) )
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f36,f61])).

fof(f36,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK1,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_partfun1(sK1,X2)
        | k1_xboole_0 = X1
        | r2_relset_1(X0,X1,sK1,X2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f27,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f15,f59])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_2)).

fof(f57,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f10,f54])).

fof(f10,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f12,f49])).

fof(f12,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f47,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f14,f44])).

fof(f14,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f9,f39])).

fof(f9,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f11,f30])).

fof(f11,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f23,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f8,f20])).

fof(f8,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
