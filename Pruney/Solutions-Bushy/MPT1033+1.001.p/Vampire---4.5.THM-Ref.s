%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1033+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 227 expanded)
%              Number of leaves         :   31 ( 104 expanded)
%              Depth                    :    9
%              Number of atoms          :  353 (1175 expanded)
%              Number of equality atoms :   42 ( 194 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f66,f71,f76,f85,f91,f109,f186,f197,f198,f199,f248,f270,f275,f341,f346,f348])).

fof(f348,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f346,plain,
    ( spl4_32
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f285,f272,f343])).

fof(f343,plain,
    ( spl4_32
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f272,plain,
    ( spl4_25
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f285,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f274,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f274,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f272])).

fof(f341,plain,
    ( spl4_31
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f281,f267,f338])).

fof(f338,plain,
    ( spl4_31
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f267,plain,
    ( spl4_24
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f281,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f269,f30])).

fof(f269,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f267])).

fof(f275,plain,
    ( spl4_25
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f231,f180,f73,f272])).

fof(f73,plain,
    ( spl4_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f180,plain,
    ( spl4_18
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f231,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f75,f181,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f181,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f75,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f270,plain,
    ( spl4_24
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f230,f180,f68,f267])).

fof(f68,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f230,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f70,f181,f33])).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f248,plain,
    ( spl4_11
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_7
    | spl4_14 ),
    inference(avatar_split_clause,[],[f201,f111,f68,f53,f38,f88])).

fof(f88,plain,
    ( spl4_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f38,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f53,plain,
    ( spl4_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f111,plain,
    ( spl4_14
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f201,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_7
    | spl4_14 ),
    inference(subsumption_resolution,[],[f200,f112])).

fof(f112,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f200,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f116,f55])).

fof(f55,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f116,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_xboole_0(sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f96,f70])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_partfun1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl4_1 ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f199,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != sK1
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f198,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f197,plain,
    ( spl4_19
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f187,f120,f111,f73,f68,f48,f43,f38,f194])).

fof(f194,plain,
    ( spl4_19
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f43,plain,
    ( spl4_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f48,plain,
    ( spl4_3
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f120,plain,
    ( spl4_15
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f187,plain,
    ( sK2 = sK3
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f40,f45,f50,f113,f70,f75,f122,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_partfun1(X3,X0)
      | ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f122,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f120])).

fof(f113,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f50,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f45,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f186,plain,
    ( spl4_15
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_8
    | spl4_11 ),
    inference(avatar_split_clause,[],[f166,f88,f73,f58,f43,f120])).

fof(f58,plain,
    ( spl4_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f166,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_8
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f60,f75,f90,f97])).

fof(f97,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_partfun1(sK3,X2)
        | ~ v1_funct_2(sK3,X2,X3)
        | v1_xboole_0(X3) )
    | ~ spl4_2 ),
    inference(resolution,[],[f32,f45])).

fof(f90,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f60,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f109,plain,
    ( spl4_13
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f93,f73,f106])).

fof(f106,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f93,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f75,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f91,plain,
    ( ~ spl4_11
    | spl4_9 ),
    inference(avatar_split_clause,[],[f86,f78,f88])).

fof(f78,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f86,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f80,f30])).

fof(f80,plain,
    ( k1_xboole_0 != sK1
    | spl4_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f85,plain,
    ( ~ spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f28,f82,f78])).

fof(f82,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f28,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f76,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f73])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f23,f68])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f63,plain,
    ( spl4_6
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f29,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
