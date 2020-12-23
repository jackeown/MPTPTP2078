%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 215 expanded)
%              Number of leaves         :   32 (  86 expanded)
%              Depth                    :    9
%              Number of atoms          :  333 ( 806 expanded)
%              Number of equality atoms :   31 (  98 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f449,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f78,f83,f88,f107,f112,f141,f150,f177,f182,f190,f195,f233,f359,f444,f445,f446,f448])).

fof(f448,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f446,plain,
    ( sK2 != k2_zfmisc_1(sK0,sK1)
    | sK3 != k2_zfmisc_1(sK0,sK1)
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f445,plain,
    ( spl6_16
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | spl6_16
    | ~ spl6_20 ),
    inference(resolution,[],[f399,f140])).

fof(f140,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_16
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f399,plain,
    ( ! [X2,X3] : r1_tarski(k2_zfmisc_1(X2,sK1),X3)
    | ~ spl6_20 ),
    inference(resolution,[],[f374,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f374,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,sK1))
    | ~ spl6_20 ),
    inference(resolution,[],[f162,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_zfmisc_1(X1,X0)) ) ),
    inference(resolution,[],[f33,f99])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f162,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl6_20
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f444,plain,
    ( spl6_18
    | ~ spl6_20 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | spl6_18
    | ~ spl6_20 ),
    inference(resolution,[],[f399,f149])).

fof(f149,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_18
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f359,plain,
    ( ~ spl6_8
    | ~ spl6_25
    | ~ spl6_5
    | spl6_41
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f355,f231,f75,f340,f70,f192,f85])).

fof(f85,plain,
    ( spl6_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f192,plain,
    ( spl6_25
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f70,plain,
    ( spl6_5
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f340,plain,
    ( spl6_41
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f75,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f231,plain,
    ( spl6_31
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK2 = X0
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_partfun1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f355,plain,
    ( sK2 = sK3
    | ~ r1_partfun1(sK2,sK3)
    | ~ v1_partfun1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(resolution,[],[f232,f77])).

fof(f77,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK2 = X0
        | ~ r1_partfun1(sK2,X0)
        | ~ v1_partfun1(X0,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f231])).

fof(f233,plain,
    ( ~ spl6_24
    | spl6_31
    | ~ spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f206,f50,f60,f231,f187])).

fof(f187,plain,
    ( spl6_24
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f60,plain,
    ( spl6_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f50,plain,
    ( spl6_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_partfun1(sK2,sK0)
        | ~ v1_partfun1(X0,sK0)
        | ~ r1_partfun1(sK2,X0)
        | sK2 = X0 )
    | ~ spl6_1 ),
    inference(resolution,[],[f42,f52])).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_partfun1(X3,X0)
      | ~ r1_partfun1(X2,X3)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f195,plain,
    ( spl6_25
    | ~ spl6_7
    | ~ spl6_8
    | spl6_20
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f184,f75,f161,f85,f80,f192])).

fof(f80,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f184,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | v1_partfun1(sK3,sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f32,f77])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f190,plain,
    ( spl6_24
    | ~ spl6_2
    | ~ spl6_3
    | spl6_20
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f183,f50,f161,f60,f55,f187])).

fof(f55,plain,
    ( spl6_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f183,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f32,f52])).

fof(f182,plain,
    ( spl6_23
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f171,f75,f179])).

fof(f179,plain,
    ( spl6_23
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f171,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f48,f77])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f177,plain,
    ( spl6_22
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f170,f50,f174])).

fof(f174,plain,
    ( spl6_22
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f170,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f48,f52])).

fof(f150,plain,
    ( spl6_17
    | ~ spl6_18
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f122,f109,f147,f143])).

fof(f143,plain,
    ( spl6_17
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f109,plain,
    ( spl6_12
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f122,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_12 ),
    inference(resolution,[],[f36,f111])).

fof(f111,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f141,plain,
    ( spl6_15
    | ~ spl6_16
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f121,f104,f138,f134])).

fof(f134,plain,
    ( spl6_15
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f104,plain,
    ( spl6_11
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f121,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_11 ),
    inference(resolution,[],[f36,f106])).

fof(f106,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f112,plain,
    ( spl6_12
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f101,f75,f109])).

fof(f101,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_6 ),
    inference(resolution,[],[f41,f77])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f107,plain,
    ( spl6_11
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f100,f50,f104])).

fof(f100,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_1 ),
    inference(resolution,[],[f41,f52])).

fof(f88,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f22,f85])).

fof(f22,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f83,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f23,f80])).

fof(f23,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f24,f75])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f25,f70])).

fof(f25,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f65,plain,
    ( spl6_4
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f26,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (2138)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.47  % (2130)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.47  % (2138)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (2140)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.48  % (2130)Refutation not found, incomplete strategy% (2130)------------------------------
% 0.21/0.48  % (2130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f449,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f78,f83,f88,f107,f112,f141,f150,f177,f182,f190,f195,f233,f359,f444,f445,f446,f448])).
% 0.21/0.49  fof(f448,plain,(
% 0.21/0.49    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f446,plain,(
% 0.21/0.49    sK2 != k2_zfmisc_1(sK0,sK1) | sK3 != k2_zfmisc_1(sK0,sK1) | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f445,plain,(
% 0.21/0.49    spl6_16 | ~spl6_20),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f438])).
% 0.21/0.49  fof(f438,plain,(
% 0.21/0.49    $false | (spl6_16 | ~spl6_20)),
% 0.21/0.49    inference(resolution,[],[f399,f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl6_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    spl6_16 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.49  fof(f399,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r1_tarski(k2_zfmisc_1(X2,sK1),X3)) ) | ~spl6_20),
% 0.21/0.49    inference(resolution,[],[f374,f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f38,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,sK1))) ) | ~spl6_20),
% 0.21/0.49    inference(resolution,[],[f162,f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0))) )),
% 0.21/0.49    inference(resolution,[],[f33,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(resolution,[],[f40,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~spl6_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl6_20 <=> v1_xboole_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.49  fof(f444,plain,(
% 0.21/0.49    spl6_18 | ~spl6_20),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f439])).
% 0.21/0.49  fof(f439,plain,(
% 0.21/0.49    $false | (spl6_18 | ~spl6_20)),
% 0.21/0.49    inference(resolution,[],[f399,f149])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl6_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f147])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    spl6_18 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f359,plain,(
% 0.21/0.49    ~spl6_8 | ~spl6_25 | ~spl6_5 | spl6_41 | ~spl6_6 | ~spl6_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f355,f231,f75,f340,f70,f192,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl6_8 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    spl6_25 <=> v1_partfun1(sK3,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl6_5 <=> r1_partfun1(sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f340,plain,(
% 0.21/0.49    spl6_41 <=> sK2 = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    spl6_31 <=> ! [X0] : (~v1_funct_1(X0) | sK2 = X0 | ~r1_partfun1(sK2,X0) | ~v1_partfun1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    sK2 = sK3 | ~r1_partfun1(sK2,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_funct_1(sK3) | (~spl6_6 | ~spl6_31)),
% 0.21/0.49    inference(resolution,[],[f232,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK2 = X0 | ~r1_partfun1(sK2,X0) | ~v1_partfun1(X0,sK0) | ~v1_funct_1(X0)) ) | ~spl6_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f231])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ~spl6_24 | spl6_31 | ~spl6_3 | ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f206,f50,f60,f231,f187])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    spl6_24 <=> v1_partfun1(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl6_3 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl6_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_partfun1(sK2,sK0) | ~v1_partfun1(X0,sK0) | ~r1_partfun1(sK2,X0) | sK2 = X0) ) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f42,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~r1_partfun1(X2,X3) | X2 = X3) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    spl6_25 | ~spl6_7 | ~spl6_8 | spl6_20 | ~spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f184,f75,f161,f85,f80,f192])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl6_7 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK1) | v1_partfun1(sK3,sK0) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f32,f77])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    spl6_24 | ~spl6_2 | ~spl6_3 | spl6_20 | ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f183,f50,f161,f60,f55,f187])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl6_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | v1_partfun1(sK2,sK0) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f32,f52])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl6_23 | ~spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f171,f75,f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl6_23 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f48,f77])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.49    inference(equality_resolution,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl6_22 | ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f170,f50,f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    spl6_22 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f48,f52])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl6_17 | ~spl6_18 | ~spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f122,f109,f147,f143])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl6_17 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl6_12 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1) | ~spl6_12),
% 0.21/0.49    inference(resolution,[],[f36,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl6_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f109])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl6_15 | ~spl6_16 | ~spl6_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f121,f104,f138,f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl6_15 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl6_11 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1) | ~spl6_11),
% 0.21/0.49    inference(resolution,[],[f36,f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl6_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl6_12 | ~spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f101,f75,f109])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f41,f77])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl6_11 | ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f100,f50,f104])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f41,f52])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl6_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f85])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl6_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f80])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f75])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f70])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    r1_partfun1(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl6_4 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f60])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f55])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f50])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (2138)------------------------------
% 0.21/0.49  % (2138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2138)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (2138)Memory used [KB]: 11001
% 0.21/0.49  % (2138)Time elapsed: 0.082 s
% 0.21/0.49  % (2138)------------------------------
% 0.21/0.49  % (2138)------------------------------
% 0.21/0.49  % (2121)Success in time 0.135 s
%------------------------------------------------------------------------------
