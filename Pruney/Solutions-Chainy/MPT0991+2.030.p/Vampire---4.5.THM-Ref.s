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
% DateTime   : Thu Dec  3 13:03:08 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 194 expanded)
%              Number of leaves         :   31 (  83 expanded)
%              Depth                    :    8
%              Number of atoms          :  342 ( 905 expanded)
%              Number of equality atoms :   58 ( 119 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f88,f93,f98,f103,f108,f113,f125,f132,f234,f238,f276,f280,f327,f333,f334])).

fof(f334,plain,
    ( k1_xboole_0 != sK2
    | v2_funct_1(sK2)
    | ~ v2_funct_1(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f333,plain,
    ( spl4_26
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f328,f324,f330])).

fof(f330,plain,
    ( spl4_26
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f324,plain,
    ( spl4_25
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f328,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_25 ),
    inference(resolution,[],[f326,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f326,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f324])).

fof(f327,plain,
    ( spl4_25
    | ~ spl4_13
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f301,f269,f129,f324])).

fof(f129,plain,
    ( spl4_13
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f269,plain,
    ( spl4_23
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f301,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f286,f62])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f286,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_13
    | ~ spl4_23 ),
    inference(superposition,[],[f131,f271])).

fof(f271,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f269])).

fof(f131,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f280,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl4_24 ),
    inference(unit_resulting_resolution,[],[f55,f275])).

fof(f275,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl4_24
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f55,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f41,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f276,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_8
    | spl4_3
    | spl4_23
    | ~ spl4_24
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f242,f231,f273,f269,f75,f100,f90,f70,f95,f85,f65])).

fof(f65,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f85,plain,
    ( spl4_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f95,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f70,plain,
    ( spl4_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f90,plain,
    ( spl4_6
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f100,plain,
    ( spl4_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f75,plain,
    ( spl4_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f231,plain,
    ( spl4_21
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f242,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_21 ),
    inference(superposition,[],[f38,f233])).

fof(f233,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f231])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f238,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_8
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_8
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f67,f72,f97,f102,f229,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f229,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl4_20
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f102,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f72,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f67,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f234,plain,
    ( ~ spl4_20
    | spl4_21
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f223,f110,f231,f227])).

fof(f110,plain,
    ( spl4_10
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f223,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_10 ),
    inference(resolution,[],[f174,f112])).

fof(f112,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f174,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f42,f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f54,f44])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f132,plain,
    ( spl4_13
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f126,f95,f129])).

fof(f126,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f52,f97])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f125,plain,
    ( spl4_12
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f115,f105,f122])).

fof(f122,plain,
    ( spl4_12
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f105,plain,
    ( spl4_9
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f115,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_9 ),
    inference(superposition,[],[f55,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f113,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f36,f110])).

fof(f36,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ v2_funct_1(X2)
        & ? [X3] :
            ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(sK2)
      & ? [X3] :
          ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ~ ( ~ v2_funct_1(X2)
            & ? [X3] :
                ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ v2_funct_1(X2)
          & ? [X3] :
              ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

fof(f108,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f50,f44])).

fof(f50,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f103,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f35,f100])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f31,f95])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f93,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f34,f90])).

fof(f34,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f30,f85])).

fof(f30,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f37,f75])).

fof(f37,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f33,f70])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:04:22 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.19/0.46  % (8755)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.47  % (8746)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.48  % (8732)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.48  % (8738)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.49  % (8755)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % (8752)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.49  % (8750)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.49  % (8735)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.49  % (8759)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.50  % (8736)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (8742)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f335,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f68,f73,f78,f88,f93,f98,f103,f108,f113,f125,f132,f234,f238,f276,f280,f327,f333,f334])).
% 0.19/0.50  fof(f334,plain,(
% 0.19/0.50    k1_xboole_0 != sK2 | v2_funct_1(sK2) | ~v2_funct_1(k1_xboole_0)),
% 0.19/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.50  fof(f333,plain,(
% 0.19/0.50    spl4_26 | ~spl4_25),
% 0.19/0.50    inference(avatar_split_clause,[],[f328,f324,f330])).
% 0.19/0.50  fof(f330,plain,(
% 0.19/0.50    spl4_26 <=> k1_xboole_0 = sK2),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.19/0.50  fof(f324,plain,(
% 0.19/0.50    spl4_25 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.19/0.50  fof(f328,plain,(
% 0.19/0.50    k1_xboole_0 = sK2 | ~spl4_25),
% 0.19/0.50    inference(resolution,[],[f326,f51])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f21])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.19/0.50  fof(f326,plain,(
% 0.19/0.50    r1_tarski(sK2,k1_xboole_0) | ~spl4_25),
% 0.19/0.50    inference(avatar_component_clause,[],[f324])).
% 0.19/0.50  fof(f327,plain,(
% 0.19/0.50    spl4_25 | ~spl4_13 | ~spl4_23),
% 0.19/0.50    inference(avatar_split_clause,[],[f301,f269,f129,f324])).
% 0.19/0.50  fof(f129,plain,(
% 0.19/0.50    spl4_13 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.19/0.50  fof(f269,plain,(
% 0.19/0.50    spl4_23 <=> k1_xboole_0 = sK0),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.19/0.50  fof(f301,plain,(
% 0.19/0.50    r1_tarski(sK2,k1_xboole_0) | (~spl4_13 | ~spl4_23)),
% 0.19/0.50    inference(forward_demodulation,[],[f286,f62])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.50    inference(equality_resolution,[],[f48])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.50    inference(flattening,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.50    inference(nnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.50  fof(f286,plain,(
% 0.19/0.50    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1)) | (~spl4_13 | ~spl4_23)),
% 0.19/0.50    inference(superposition,[],[f131,f271])).
% 0.19/0.50  fof(f271,plain,(
% 0.19/0.50    k1_xboole_0 = sK0 | ~spl4_23),
% 0.19/0.50    inference(avatar_component_clause,[],[f269])).
% 0.19/0.50  fof(f131,plain,(
% 0.19/0.50    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl4_13),
% 0.19/0.50    inference(avatar_component_clause,[],[f129])).
% 0.19/0.50  fof(f280,plain,(
% 0.19/0.50    spl4_24),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f277])).
% 0.19/0.50  fof(f277,plain,(
% 0.19/0.50    $false | spl4_24),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f55,f275])).
% 0.19/0.50  fof(f275,plain,(
% 0.19/0.50    ~v2_funct_1(k6_partfun1(sK0)) | spl4_24),
% 0.19/0.50    inference(avatar_component_clause,[],[f273])).
% 0.19/0.50  fof(f273,plain,(
% 0.19/0.50    spl4_24 <=> v2_funct_1(k6_partfun1(sK0))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.19/0.50    inference(definition_unfolding,[],[f41,f44])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.19/0.50  fof(f276,plain,(
% 0.19/0.50    ~spl4_1 | ~spl4_5 | ~spl4_7 | ~spl4_2 | ~spl4_6 | ~spl4_8 | spl4_3 | spl4_23 | ~spl4_24 | ~spl4_21),
% 0.19/0.50    inference(avatar_split_clause,[],[f242,f231,f273,f269,f75,f100,f90,f70,f95,f85,f65])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    spl4_1 <=> v1_funct_1(sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    spl4_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    spl4_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.50  fof(f70,plain,(
% 0.19/0.50    spl4_2 <=> v1_funct_1(sK3)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.50  fof(f90,plain,(
% 0.19/0.50    spl4_6 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.50  fof(f100,plain,(
% 0.19/0.50    spl4_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    spl4_3 <=> v2_funct_1(sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.50  fof(f231,plain,(
% 0.19/0.50    spl4_21 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.19/0.50  fof(f242,plain,(
% 0.19/0.50    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_21),
% 0.19/0.50    inference(superposition,[],[f38,f233])).
% 0.19/0.50  fof(f233,plain,(
% 0.19/0.50    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_21),
% 0.19/0.50    inference(avatar_component_clause,[],[f231])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.50    inference(flattening,[],[f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 0.19/0.50  fof(f238,plain,(
% 0.19/0.50    ~spl4_1 | ~spl4_2 | ~spl4_7 | ~spl4_8 | spl4_20),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f235])).
% 0.19/0.50  fof(f235,plain,(
% 0.19/0.50    $false | (~spl4_1 | ~spl4_2 | ~spl4_7 | ~spl4_8 | spl4_20)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f67,f72,f97,f102,f229,f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f20])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.19/0.50    inference(flattening,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.19/0.50    inference(ennf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.19/0.50  fof(f229,plain,(
% 0.19/0.50    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_20),
% 0.19/0.50    inference(avatar_component_clause,[],[f227])).
% 0.19/0.50  fof(f227,plain,(
% 0.19/0.50    spl4_20 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.19/0.50  fof(f102,plain,(
% 0.19/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_8),
% 0.19/0.50    inference(avatar_component_clause,[],[f100])).
% 0.19/0.50  fof(f97,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 0.19/0.50    inference(avatar_component_clause,[],[f95])).
% 0.19/0.50  fof(f72,plain,(
% 0.19/0.50    v1_funct_1(sK3) | ~spl4_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f70])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    v1_funct_1(sK2) | ~spl4_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f65])).
% 0.19/0.50  fof(f234,plain,(
% 0.19/0.50    ~spl4_20 | spl4_21 | ~spl4_10),
% 0.19/0.50    inference(avatar_split_clause,[],[f223,f110,f231,f227])).
% 0.19/0.50  fof(f110,plain,(
% 0.19/0.50    spl4_10 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.50  fof(f223,plain,(
% 0.19/0.50    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_10),
% 0.19/0.50    inference(resolution,[],[f174,f112])).
% 0.19/0.50  fof(f112,plain,(
% 0.19/0.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_10),
% 0.19/0.50    inference(avatar_component_clause,[],[f110])).
% 0.19/0.50  fof(f174,plain,(
% 0.19/0.50    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.19/0.50    inference(resolution,[],[f42,f58])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.50    inference(definition_unfolding,[],[f54,f44])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.19/0.50  fof(f42,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(nnf_transformation,[],[f18])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(flattening,[],[f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.19/0.50  fof(f132,plain,(
% 0.19/0.50    spl4_13 | ~spl4_7),
% 0.19/0.50    inference(avatar_split_clause,[],[f126,f95,f129])).
% 0.19/0.50  fof(f126,plain,(
% 0.19/0.50    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl4_7),
% 0.19/0.50    inference(resolution,[],[f52,f97])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.50    inference(nnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.50  fof(f125,plain,(
% 0.19/0.50    spl4_12 | ~spl4_9),
% 0.19/0.50    inference(avatar_split_clause,[],[f115,f105,f122])).
% 0.19/0.50  fof(f122,plain,(
% 0.19/0.50    spl4_12 <=> v2_funct_1(k1_xboole_0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.19/0.50  fof(f105,plain,(
% 0.19/0.50    spl4_9 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.50  fof(f115,plain,(
% 0.19/0.50    v2_funct_1(k1_xboole_0) | ~spl4_9),
% 0.19/0.50    inference(superposition,[],[f55,f107])).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl4_9),
% 0.19/0.50    inference(avatar_component_clause,[],[f105])).
% 0.19/0.50  fof(f113,plain,(
% 0.19/0.50    spl4_10),
% 0.19/0.50    inference(avatar_split_clause,[],[f36,f110])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ~v2_funct_1(sK2) & (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f23,f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~v2_funct_1(sK2) & ? [X3] : (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ? [X3] : (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.19/0.50    inference(flattening,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ? [X0,X1,X2] : ((~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.50    inference(ennf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 0.19/0.50    inference(negated_conjecture,[],[f11])).
% 0.19/0.50  fof(f11,conjecture,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).
% 0.19/0.50  fof(f108,plain,(
% 0.19/0.50    spl4_9),
% 0.19/0.50    inference(avatar_split_clause,[],[f57,f105])).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.19/0.50    inference(definition_unfolding,[],[f50,f44])).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.50    inference(cnf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.19/0.50  fof(f103,plain,(
% 0.19/0.50    spl4_8),
% 0.19/0.50    inference(avatar_split_clause,[],[f35,f100])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f98,plain,(
% 0.19/0.50    spl4_7),
% 0.19/0.50    inference(avatar_split_clause,[],[f31,f95])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    spl4_6),
% 0.19/0.50    inference(avatar_split_clause,[],[f34,f90])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    v1_funct_2(sK3,sK1,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f88,plain,(
% 0.19/0.50    spl4_5),
% 0.19/0.50    inference(avatar_split_clause,[],[f30,f85])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f78,plain,(
% 0.19/0.50    ~spl4_3),
% 0.19/0.50    inference(avatar_split_clause,[],[f37,f75])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ~v2_funct_1(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f73,plain,(
% 0.19/0.50    spl4_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f33,f70])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    v1_funct_1(sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    spl4_1),
% 0.19/0.50    inference(avatar_split_clause,[],[f29,f65])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    v1_funct_1(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f24])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (8755)------------------------------
% 0.19/0.50  % (8755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (8755)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (8755)Memory used [KB]: 11001
% 0.19/0.50  % (8755)Time elapsed: 0.073 s
% 0.19/0.50  % (8755)------------------------------
% 0.19/0.50  % (8755)------------------------------
% 0.19/0.50  % (8728)Success in time 0.155 s
%------------------------------------------------------------------------------
