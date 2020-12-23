%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 215 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :    7
%              Number of atoms          :  334 (1079 expanded)
%              Number of equality atoms :   28 ( 159 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f56,f61,f66,f71,f76,f81,f86,f107,f125,f140,f173,f178,f179,f218,f223,f265])).

fof(f265,plain,
    ( spl5_11
    | ~ spl5_26
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl5_11
    | ~ spl5_26
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f256,f222])).

fof(f222,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl5_27
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f256,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_11
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f92,f217,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f217,plain,
    ( v1_xboole_0(sK3)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl5_26
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f92,plain,
    ( sK2 != sK3
    | spl5_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_11
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f223,plain,
    ( spl5_27
    | ~ spl5_8
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f200,f170,f73,f220])).

fof(f73,plain,
    ( spl5_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f170,plain,
    ( spl5_23
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f200,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_8
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f75,f172,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f172,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f170])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f218,plain,
    ( spl5_26
    | ~ spl5_5
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f201,f170,f58,f215])).

fof(f58,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f201,plain,
    ( v1_xboole_0(sK3)
    | ~ spl5_5
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f60,f172,f35])).

fof(f60,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f179,plain,
    ( ~ spl5_19
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | spl5_11
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f176,f128,f91,f83,f73,f68,f58,f53,f148])).

fof(f148,plain,
    ( spl5_19
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f53,plain,
    ( spl5_4
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f68,plain,
    ( spl5_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f83,plain,
    ( spl5_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f128,plain,
    ( spl5_16
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f176,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | spl5_11
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f85,f70,f92,f55,f60,f75,f129,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_funct_1(X3)
      | X2 = X3
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f129,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f55,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f70,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f85,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f178,plain,
    ( spl5_23
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_19 ),
    inference(avatar_split_clause,[],[f177,f148,f68,f63,f58,f170])).

fof(f63,plain,
    ( spl5_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f177,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_19 ),
    inference(unit_resulting_resolution,[],[f70,f65,f60,f150,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f150,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f148])).

fof(f65,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f173,plain,
    ( spl5_23
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_16 ),
    inference(avatar_split_clause,[],[f168,f128,f83,f78,f73,f170])).

fof(f78,plain,
    ( spl5_9
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f168,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f85,f80,f75,f130,f34])).

fof(f130,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f80,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f140,plain,
    ( ~ spl5_15
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f119,f73,f121])).

fof(f121,plain,
    ( spl5_15
  <=> sP4(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f119,plain,
    ( ~ sP4(sK1,sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f75,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP4(X1,X0) ) ),
    inference(general_splitting,[],[f30,f36_D])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP4(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f36_D])).

fof(f36_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP4(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f125,plain,
    ( spl5_15
    | ~ spl5_8
    | spl5_13 ),
    inference(avatar_split_clause,[],[f115,f104,f73,f121])).

fof(f104,plain,
    ( spl5_13
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f115,plain,
    ( sP4(sK1,sK0)
    | ~ spl5_8
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f106,f75,f36])).

fof(f106,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f107,plain,
    ( ~ spl5_13
    | spl5_1
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f98,f91,f39,f104])).

fof(f39,plain,
    ( spl5_1
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f98,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl5_1
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f41,f93])).

fof(f93,plain,
    ( sK2 = sK3
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f41,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f86,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f21,f83])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f81,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f22,f78])).

fof(f22,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f23,f73])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f24,f68])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

% (17521)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f42,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f39])).

fof(f29,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:58:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (17534)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (17534)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f42,f56,f61,f66,f71,f76,f81,f86,f107,f125,f140,f173,f178,f179,f218,f223,f265])).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    spl5_11 | ~spl5_26 | ~spl5_27),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f264])).
% 0.20/0.48  fof(f264,plain,(
% 0.20/0.48    $false | (spl5_11 | ~spl5_26 | ~spl5_27)),
% 0.20/0.48    inference(subsumption_resolution,[],[f256,f222])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    v1_xboole_0(sK2) | ~spl5_27),
% 0.20/0.48    inference(avatar_component_clause,[],[f220])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    spl5_27 <=> v1_xboole_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.20/0.48  fof(f256,plain,(
% 0.20/0.48    ~v1_xboole_0(sK2) | (spl5_11 | ~spl5_26)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f92,f217,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~v1_xboole_0(X0) | X0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    v1_xboole_0(sK3) | ~spl5_26),
% 0.20/0.48    inference(avatar_component_clause,[],[f215])).
% 0.20/0.48  fof(f215,plain,(
% 0.20/0.48    spl5_26 <=> v1_xboole_0(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    sK2 != sK3 | spl5_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f91])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    spl5_11 <=> sK2 = sK3),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.48  fof(f223,plain,(
% 0.20/0.48    spl5_27 | ~spl5_8 | ~spl5_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f200,f170,f73,f220])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    spl5_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    spl5_23 <=> v1_xboole_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    v1_xboole_0(sK2) | (~spl5_8 | ~spl5_23)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f75,f172,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | ~spl5_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f170])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f73])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    spl5_26 | ~spl5_5 | ~spl5_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f201,f170,f58,f215])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    v1_xboole_0(sK3) | (~spl5_5 | ~spl5_23)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f60,f172,f35])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f58])).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    ~spl5_19 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | spl5_11 | ~spl5_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f176,f128,f91,f83,f73,f68,f58,f53,f148])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    spl5_19 <=> v1_partfun1(sK3,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl5_4 <=> r1_partfun1(sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl5_7 <=> v1_funct_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl5_10 <=> v1_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    spl5_16 <=> v1_partfun1(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    ~v1_partfun1(sK3,sK0) | (~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | spl5_11 | ~spl5_16)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f85,f70,f92,f55,f60,f75,f129,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~v1_funct_1(X3) | X2 = X3 | ~v1_funct_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    v1_partfun1(sK2,sK0) | ~spl5_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f128])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    r1_partfun1(sK2,sK3) | ~spl5_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f53])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    v1_funct_1(sK3) | ~spl5_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f68])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    v1_funct_1(sK2) | ~spl5_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f83])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    spl5_23 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_19),
% 0.20/0.48    inference(avatar_split_clause,[],[f177,f148,f68,f63,f58,f170])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl5_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | (~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_19)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f70,f65,f60,f150,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    ~v1_partfun1(sK3,sK0) | spl5_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f148])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK0,sK1) | ~spl5_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f63])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    spl5_23 | ~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f168,f128,f83,f78,f73,f170])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl5_9 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | (~spl5_8 | ~spl5_9 | ~spl5_10 | spl5_16)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f85,f80,f75,f130,f34])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ~v1_partfun1(sK2,sK0) | spl5_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f128])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    v1_funct_2(sK2,sK0,sK1) | ~spl5_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f78])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ~spl5_15 | ~spl5_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f119,f73,f121])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    spl5_15 <=> sP4(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ~sP4(sK1,sK0) | ~spl5_8),
% 0.20/0.48    inference(resolution,[],[f75,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP4(X1,X0)) )),
% 0.20/0.48    inference(general_splitting,[],[f30,f36_D])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP4(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36_D])).
% 0.20/0.48  fof(f36_D,plain,(
% 0.20/0.48    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP4(X1,X0)) )),
% 0.20/0.48    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    spl5_15 | ~spl5_8 | spl5_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f115,f104,f73,f121])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    spl5_13 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    sP4(sK1,sK0) | (~spl5_8 | spl5_13)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f106,f75,f36])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl5_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f104])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ~spl5_13 | spl5_1 | ~spl5_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f98,f91,f39,f104])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    spl5_1 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK1,sK2,sK2) | (spl5_1 | ~spl5_11)),
% 0.20/0.48    inference(backward_demodulation,[],[f41,f93])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    sK2 = sK3 | ~spl5_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f91])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK1,sK2,sK3) | spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f39])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    spl5_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f83])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f19,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    spl5_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f78])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl5_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f73])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    spl5_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f24,f68])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    v1_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl5_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f63])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl5_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f26,f58])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f53])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    r1_partfun1(sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  % (17521)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ~spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f39])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17534)------------------------------
% 0.20/0.48  % (17534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17534)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17534)Memory used [KB]: 6268
% 0.20/0.48  % (17534)Time elapsed: 0.069 s
% 0.20/0.48  % (17534)------------------------------
% 0.20/0.48  % (17534)------------------------------
% 0.20/0.49  % (17520)Success in time 0.123 s
%------------------------------------------------------------------------------
