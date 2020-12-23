%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 151 expanded)
%              Number of leaves         :   24 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  267 ( 398 expanded)
%              Number of equality atoms :   50 (  81 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f63,f68,f78,f97,f106,f110,f148,f156,f192,f202,f210,f237])).

fof(f237,plain,
    ( ~ spl4_3
    | spl4_9
    | ~ spl4_19
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl4_3
    | spl4_9
    | ~ spl4_19
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f235,f105])).

fof(f105,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_9
  <=> k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f235,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ spl4_3
    | ~ spl4_19
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f205,f209])).

fof(f209,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl4_26
  <=> sK3 = k7_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f205,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(resolution,[],[f155,f62])).

fof(f62,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_3
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f210,plain,
    ( spl4_26
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f203,f200,f207])).

fof(f200,plain,
    ( spl4_25
  <=> ! [X1] :
        ( sK3 = k7_relat_1(sK3,X1)
        | ~ r1_tarski(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f203,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_25 ),
    inference(resolution,[],[f201,f44])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f201,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | sK3 = k7_relat_1(sK3,X1) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( spl4_25
    | ~ spl4_2
    | ~ spl4_17
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f196,f190,f146,f54,f200])).

fof(f54,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f146,plain,
    ( spl4_17
  <=> ! [X0] :
        ( r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f190,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( ~ r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | k7_relat_1(sK3,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f196,plain,
    ( ! [X1] :
        ( sK3 = k7_relat_1(sK3,X1)
        | ~ r1_tarski(sK2,X1) )
    | ~ spl4_2
    | ~ spl4_17
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f195,f56])).

fof(f56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f195,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | sK3 = k7_relat_1(sK3,X1)
        | ~ r1_tarski(sK2,X1) )
    | ~ spl4_17
    | ~ spl4_24 ),
    inference(resolution,[],[f191,f147])).

fof(f147,plain,
    ( ! [X0] :
        ( r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | k7_relat_1(sK3,X0) = X1 )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( spl4_24
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f111,f108,f190])).

fof(f108,plain,
    ( spl4_10
  <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | k7_relat_1(sK3,X0) = X1 )
    | ~ spl4_10 ),
    inference(resolution,[],[f109,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f109,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f156,plain,
    ( spl4_19
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f80,f75,f154])).

fof(f75,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f77,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f77,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f148,plain,
    ( spl4_17
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f100,f95,f54,f146])).

fof(f95,plain,
    ( spl4_8
  <=> ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f100,plain,
    ( ! [X0] :
        ( r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f99,f56])).

fof(f99,plain,
    ( ! [X0] :
        ( r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK2,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) )
    | ~ spl4_8 ),
    inference(superposition,[],[f41,f96])).

fof(f96,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

fof(f110,plain,
    ( spl4_10
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f101,f95,f54,f108])).

fof(f101,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f88,f96])).

fof(f88,plain,
    ( ! [X0] : m1_subset_1(k5_relset_1(sK2,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f40,f56])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relset_1)).

fof(f106,plain,
    ( ~ spl4_9
    | spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f98,f95,f65,f103])).

fof(f65,plain,
    ( spl4_4
  <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f98,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_4
    | ~ spl4_8 ),
    inference(superposition,[],[f67,f96])).

fof(f67,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f97,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f82,f54,f95])).

fof(f82,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)
    | ~ spl4_2 ),
    inference(resolution,[],[f39,f56])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f78,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f72,f54,f75])).

fof(f72,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f56])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f68,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
        & r1_xboole_0(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

fof(f63,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f58,f49,f60])).

fof(f49,plain,
    ( spl4_1
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f58,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f34,f51])).

fof(f51,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f57,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f30,f49])).

fof(f30,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (11882)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (11893)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (11886)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (11892)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (11884)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (11884)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f52,f57,f63,f68,f78,f97,f106,f110,f148,f156,f192,f202,f210,f237])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    ~spl4_3 | spl4_9 | ~spl4_19 | ~spl4_26),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    $false | (~spl4_3 | spl4_9 | ~spl4_19 | ~spl4_26)),
% 0.21/0.52    inference(subsumption_resolution,[],[f235,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(sK3,sK1) | spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl4_9 <=> k1_xboole_0 = k7_relat_1(sK3,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK3,sK1) | (~spl4_3 | ~spl4_19 | ~spl4_26)),
% 0.21/0.52    inference(forward_demodulation,[],[f205,f209])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    sK3 = k7_relat_1(sK3,sK2) | ~spl4_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    spl4_26 <=> sK3 = k7_relat_1(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1) | (~spl4_3 | ~spl4_19)),
% 0.21/0.52    inference(resolution,[],[f155,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    r1_xboole_0(sK2,sK1) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    spl4_3 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1)) ) | ~spl4_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    spl4_19 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    spl4_26 | ~spl4_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f203,f200,f207])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    spl4_25 <=> ! [X1] : (sK3 = k7_relat_1(sK3,X1) | ~r1_tarski(sK2,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    sK3 = k7_relat_1(sK3,sK2) | ~spl4_25),
% 0.21/0.52    inference(resolution,[],[f201,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tarski(sK2,X1) | sK3 = k7_relat_1(sK3,X1)) ) | ~spl4_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f200])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    spl4_25 | ~spl4_2 | ~spl4_17 | ~spl4_24),
% 0.21/0.52    inference(avatar_split_clause,[],[f196,f190,f146,f54,f200])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    spl4_17 <=> ! [X0] : (r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),sK3) | ~r1_tarski(sK2,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    spl4_24 <=> ! [X1,X0] : (~r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k7_relat_1(sK3,X0) = X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ( ! [X1] : (sK3 = k7_relat_1(sK3,X1) | ~r1_tarski(sK2,X1)) ) | (~spl4_2 | ~spl4_17 | ~spl4_24)),
% 0.21/0.52    inference(subsumption_resolution,[],[f195,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | sK3 = k7_relat_1(sK3,X1) | ~r1_tarski(sK2,X1)) ) | (~spl4_17 | ~spl4_24)),
% 0.21/0.52    inference(resolution,[],[f191,f147])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ( ! [X0] : (r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),sK3) | ~r1_tarski(sK2,X0)) ) | ~spl4_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f146])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k7_relat_1(sK3,X0) = X1) ) | ~spl4_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f190])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    spl4_24 | ~spl4_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f111,f108,f190])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl4_10 <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | k7_relat_1(sK3,X0) = X1) ) | ~spl4_10),
% 0.21/0.52    inference(resolution,[],[f109,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | ~spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f108])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl4_19 | ~spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f80,f75,f154])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl4_5 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,X0),X1)) ) | ~spl4_5),
% 0.21/0.52    inference(resolution,[],[f77,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X0,X1) | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl4_17 | ~spl4_2 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f100,f95,f54,f146])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl4_8 <=> ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0] : (r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),sK3) | ~r1_tarski(sK2,X0)) ) | (~spl4_2 | ~spl4_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f56])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X0] : (r2_relset_1(sK2,sK0,k7_relat_1(sK3,X0),sK3) | ~r1_tarski(sK2,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | ~spl4_8),
% 0.21/0.52    inference(superposition,[],[f41,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)) ) | ~spl4_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f95])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl4_10 | ~spl4_2 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f101,f95,f54,f108])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | (~spl4_2 | ~spl4_8)),
% 0.21/0.52    inference(forward_demodulation,[],[f88,f96])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k5_relset_1(sK2,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))) ) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f40,f56])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k5_relset_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relset_1)).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ~spl4_9 | spl4_4 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f98,f95,f65,f103])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl4_4 <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(sK3,sK1) | (spl4_4 | ~spl4_8)),
% 0.21/0.52    inference(superposition,[],[f67,f96])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) | spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl4_8 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f82,f54,f95])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)) ) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f39,f56])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl4_5 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f72,f54,f75])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f70,f56])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f32,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f65])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl4_3 | ~spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f58,f49,f60])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl4_1 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    r1_xboole_0(sK2,sK1) | ~spl4_1),
% 0.21/0.52    inference(resolution,[],[f34,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    r1_xboole_0(sK1,sK2) | ~spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f49])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f54])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f49])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    r1_xboole_0(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (11884)------------------------------
% 0.21/0.52  % (11884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11884)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (11884)Memory used [KB]: 6268
% 0.21/0.52  % (11884)Time elapsed: 0.104 s
% 0.21/0.52  % (11884)------------------------------
% 0.21/0.52  % (11884)------------------------------
% 0.21/0.52  % (11904)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (11883)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (11902)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (11895)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (11897)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (11881)Success in time 0.166 s
%------------------------------------------------------------------------------
