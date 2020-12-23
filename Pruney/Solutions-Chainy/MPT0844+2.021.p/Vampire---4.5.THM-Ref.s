%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 142 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  227 ( 339 expanded)
%              Number of equality atoms :   55 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f54,f61,f67,f79,f111,f122,f161,f227,f244,f263,f268,f316])).

fof(f316,plain,
    ( ~ spl4_3
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(resolution,[],[f262,f46])).

fof(f46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f262,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl4_36
  <=> ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f268,plain,
    ( ~ spl4_3
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f266,f24])).

fof(f24,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f266,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(resolution,[],[f110,f46])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f263,plain,
    ( spl4_36
    | spl4_32 ),
    inference(avatar_split_clause,[],[f259,f241,f261])).

fof(f241,plain,
    ( spl4_32
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f259,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | spl4_32 ),
    inference(resolution,[],[f243,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f243,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f241])).

fof(f244,plain,
    ( ~ spl4_32
    | spl4_6
    | ~ spl4_9
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f239,f224,f82,f64,f241])).

fof(f64,plain,
    ( spl4_6
  <=> k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f82,plain,
    ( spl4_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f224,plain,
    ( spl4_30
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f239,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | spl4_6
    | ~ spl4_9
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f238,f83])).

fof(f83,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f238,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | spl4_6
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f235,f66])).

fof(f66,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f235,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ v4_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_30 ),
    inference(superposition,[],[f226,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f226,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f224])).

fof(f227,plain,
    ( spl4_30
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f222,f158,f51,f224])).

fof(f51,plain,
    ( spl4_4
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f158,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( k3_xboole_0(X1,X0) != k1_xboole_0
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f222,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(trivial_inequality_removal,[],[f221])).

fof(f221,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(superposition,[],[f159,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X1,X0) != k1_xboole_0
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f158])).

fof(f161,plain,
    ( spl4_21
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f154,f120,f158])).

fof(f120,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f154,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != k3_xboole_0(X3,X2)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X2),X3) )
    | ~ spl4_16 ),
    inference(superposition,[],[f121,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f121,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl4_16
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f113,f77,f120])).

fof(f77,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl4_8 ),
    inference(resolution,[],[f78,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f111,plain,
    ( spl4_14
    | spl4_9 ),
    inference(avatar_split_clause,[],[f107,f82,f109])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_9 ),
    inference(resolution,[],[f84,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f84,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f79,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f75,f44,f77])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f74,f24])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1)
        | ~ r1_xboole_0(X0,X1)
        | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f56,f46])).

fof(f56,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X6,X4),X5)
      | ~ r1_xboole_0(X4,X5)
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f29,f23])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f67,plain,
    ( ~ spl4_6
    | spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f62,f59,f34,f64])).

fof(f34,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f59,plain,
    ( spl4_5
  <=> ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f62,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_1
    | ~ spl4_5 ),
    inference(superposition,[],[f36,f60])).

fof(f60,plain,
    ( ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f36,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f61,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f57,f44,f59])).

fof(f57,plain,
    ( ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f32,f46])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f54,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f48,f39,f51])).

fof(f39,plain,
    ( spl4_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f48,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f28,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

fof(f42,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f34])).

fof(f22,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (23970)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.41  % (23967)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (23965)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.42  % (23962)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.42  % (23966)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.43  % (23962)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f317,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f37,f42,f47,f54,f61,f67,f79,f111,f122,f161,f227,f244,f263,f268,f316])).
% 0.20/0.43  fof(f316,plain,(
% 0.20/0.43    ~spl4_3 | ~spl4_36),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f315])).
% 0.20/0.43  fof(f315,plain,(
% 0.20/0.43    $false | (~spl4_3 | ~spl4_36)),
% 0.20/0.43    inference(resolution,[],[f262,f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.43  fof(f262,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | ~spl4_36),
% 0.20/0.43    inference(avatar_component_clause,[],[f261])).
% 0.20/0.43  fof(f261,plain,(
% 0.20/0.43    spl4_36 <=> ! [X0] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.43  fof(f268,plain,(
% 0.20/0.43    ~spl4_3 | ~spl4_14),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f267])).
% 0.20/0.43  fof(f267,plain,(
% 0.20/0.43    $false | (~spl4_3 | ~spl4_14)),
% 0.20/0.43    inference(subsumption_resolution,[],[f266,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.43  fof(f266,plain,(
% 0.20/0.43    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | (~spl4_3 | ~spl4_14)),
% 0.20/0.43    inference(resolution,[],[f110,f46])).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl4_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f109])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    spl4_14 <=> ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.43  fof(f263,plain,(
% 0.20/0.43    spl4_36 | spl4_32),
% 0.20/0.43    inference(avatar_split_clause,[],[f259,f241,f261])).
% 0.20/0.43  fof(f241,plain,(
% 0.20/0.43    spl4_32 <=> v4_relat_1(sK3,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.43  fof(f259,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | spl4_32),
% 0.20/0.43    inference(resolution,[],[f243,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.43  fof(f243,plain,(
% 0.20/0.43    ~v4_relat_1(sK3,sK2) | spl4_32),
% 0.20/0.43    inference(avatar_component_clause,[],[f241])).
% 0.20/0.43  fof(f244,plain,(
% 0.20/0.43    ~spl4_32 | spl4_6 | ~spl4_9 | ~spl4_30),
% 0.20/0.43    inference(avatar_split_clause,[],[f239,f224,f82,f64,f241])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl4_6 <=> k1_xboole_0 = k7_relat_1(sK3,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    spl4_9 <=> v1_relat_1(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.43  fof(f224,plain,(
% 0.20/0.43    spl4_30 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.43  fof(f239,plain,(
% 0.20/0.43    ~v4_relat_1(sK3,sK2) | (spl4_6 | ~spl4_9 | ~spl4_30)),
% 0.20/0.43    inference(subsumption_resolution,[],[f238,f83])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    v1_relat_1(sK3) | ~spl4_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f82])).
% 0.20/0.43  fof(f238,plain,(
% 0.20/0.43    ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | (spl4_6 | ~spl4_30)),
% 0.20/0.43    inference(subsumption_resolution,[],[f235,f66])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    k1_xboole_0 != k7_relat_1(sK3,sK1) | spl4_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f64])).
% 0.20/0.43  fof(f235,plain,(
% 0.20/0.43    k1_xboole_0 = k7_relat_1(sK3,sK1) | ~v4_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | ~spl4_30),
% 0.20/0.43    inference(superposition,[],[f226,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.43  fof(f226,plain,(
% 0.20/0.43    k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1) | ~spl4_30),
% 0.20/0.43    inference(avatar_component_clause,[],[f224])).
% 0.20/0.43  fof(f227,plain,(
% 0.20/0.43    spl4_30 | ~spl4_4 | ~spl4_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f222,f158,f51,f224])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl4_4 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.43  fof(f158,plain,(
% 0.20/0.43    spl4_21 <=> ! [X1,X0] : (k3_xboole_0(X1,X0) != k1_xboole_0 | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.43  fof(f222,plain,(
% 0.20/0.43    k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1) | (~spl4_4 | ~spl4_21)),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f221])).
% 0.20/0.43  fof(f221,plain,(
% 0.20/0.43    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1) | (~spl4_4 | ~spl4_21)),
% 0.20/0.43    inference(superposition,[],[f159,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl4_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f51])).
% 0.20/0.43  fof(f159,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X1,X0) != k1_xboole_0 | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1)) ) | ~spl4_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f158])).
% 0.20/0.43  fof(f161,plain,(
% 0.20/0.43    spl4_21 | ~spl4_16),
% 0.20/0.43    inference(avatar_split_clause,[],[f154,f120,f158])).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    spl4_16 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    ( ! [X2,X3] : (k1_xboole_0 != k3_xboole_0(X3,X2) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X2),X3)) ) | ~spl4_16),
% 0.20/0.43    inference(superposition,[],[f121,f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1)) ) | ~spl4_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f120])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    spl4_16 | ~spl4_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f113,f77,f120])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    spl4_8 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) | k3_xboole_0(X0,X1) != k1_xboole_0) ) | ~spl4_8),
% 0.20/0.43    inference(resolution,[],[f78,f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1)) ) | ~spl4_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f77])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    spl4_14 | spl4_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f107,f82,f109])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_9),
% 0.20/0.43    inference(resolution,[],[f84,f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    ~v1_relat_1(sK3) | spl4_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f82])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    spl4_8 | ~spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f75,f44,f77])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) | ~r1_xboole_0(X0,X1)) ) | ~spl4_3),
% 0.20/0.43    inference(subsumption_resolution,[],[f74,f24])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(k2_zfmisc_1(sK2,sK0))) ) | ~spl4_3),
% 0.20/0.43    inference(resolution,[],[f56,f46])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(X7)) | k1_xboole_0 = k7_relat_1(k7_relat_1(X6,X4),X5) | ~r1_xboole_0(X4,X5) | ~v1_relat_1(X7)) )),
% 0.20/0.43    inference(resolution,[],[f29,f23])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(flattening,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ~spl4_6 | spl4_1 | ~spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f62,f59,f34,f64])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    spl4_1 <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl4_5 <=> ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    k1_xboole_0 != k7_relat_1(sK3,sK1) | (spl4_1 | ~spl4_5)),
% 0.20/0.43    inference(superposition,[],[f36,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ( ! [X0] : (k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)) ) | ~spl4_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f59])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) | spl4_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f34])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    spl4_5 | ~spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f57,f44,f59])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ( ! [X0] : (k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)) ) | ~spl4_3),
% 0.20/0.43    inference(resolution,[],[f32,f46])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl4_4 | ~spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f48,f39,f51])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    spl4_2 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl4_2),
% 0.20/0.43    inference(resolution,[],[f28,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    r1_xboole_0(sK1,sK2) | ~spl4_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f39])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f20,f44])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.43    inference(flattening,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.20/0.43    inference(negated_conjecture,[],[f9])).
% 0.20/0.43  fof(f9,conjecture,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f39])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    r1_xboole_0(sK1,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ~spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f34])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (23962)------------------------------
% 0.20/0.43  % (23962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (23962)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (23962)Memory used [KB]: 10746
% 0.20/0.43  % (23962)Time elapsed: 0.033 s
% 0.20/0.43  % (23962)------------------------------
% 0.20/0.43  % (23962)------------------------------
% 0.20/0.43  % (23960)Success in time 0.082 s
%------------------------------------------------------------------------------
