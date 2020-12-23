%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:34 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 160 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :    7
%              Number of atoms          :  279 ( 464 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f56,f60,f64,f68,f72,f76,f80,f84,f90,f99,f120,f131,f138,f144,f147,f150])).

fof(f150,plain,
    ( spl4_2
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl4_2
    | ~ spl4_15
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f148,f98])).

fof(f98,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_15
  <=> r1_tarski(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f148,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | spl4_2
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f37,f137])).

fof(f137,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_22
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f37,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_2
  <=> r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f147,plain,
    ( spl4_1
    | ~ spl4_21
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl4_1
    | ~ spl4_21
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f145,f130])).

fof(f130,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_21
  <=> r1_tarski(sK2,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f145,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_1
    | ~ spl4_23 ),
    inference(superposition,[],[f33,f143])).

fof(f143,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_23
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f33,plain,
    ( ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl4_1
  <=> r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f144,plain,
    ( spl4_23
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f139,f82,f45,f141])).

fof(f45,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f82,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f139,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(resolution,[],[f83,f47])).

fof(f47,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f82])).

fof(f138,plain,
    ( spl4_22
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f133,f78,f45,f135])).

fof(f78,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f133,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(resolution,[],[f79,f47])).

fof(f79,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f131,plain,
    ( spl4_21
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f126,f118,f87,f40,f128])).

fof(f40,plain,
    ( spl4_3
  <=> r1_tarski(k6_relat_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f87,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f118,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k1_relat_1(X1))
        | ~ r1_tarski(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f126,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f125,f89])).

fof(f89,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f87])).

fof(f125,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(resolution,[],[f119,f42])).

fof(f42,plain,
    ( r1_tarski(k6_relat_1(sK2),sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k6_relat_1(X0),X1)
        | r1_tarski(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( spl4_19
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f116,f70,f62,f54,f118])).

fof(f54,plain,
    ( spl4_6
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f62,plain,
    ( spl4_8
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f70,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k1_relat_1(X1))
        | ~ r1_tarski(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f114,f63])).

fof(f63,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(X1)) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f71,f55])).

fof(f55,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f99,plain,
    ( spl4_15
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f94,f87,f66,f58,f54,f40,f96])).

fof(f58,plain,
    ( spl4_7
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f66,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f94,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f93,f59])).

fof(f59,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f93,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f92,f55])).

fof(f92,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3))
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f91,f89])).

fof(f91,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_relat_1(sK2))
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f67,f42])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f90,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f85,f74,f45,f87])).

fof(f74,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f85,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(resolution,[],[f75,f47])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f84,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f29,f82])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f80,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f28,f78])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f76,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f27,f74])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f72,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f25,f70])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f68,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f26,f66])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f60,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f56,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f48,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
        | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

fof(f43,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f20,f35,f31])).

fof(f20,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:00:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (29297)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.13/0.42  % (29291)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.42  % (29290)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.13/0.42  % (29291)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f152,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(avatar_sat_refutation,[],[f38,f43,f48,f56,f60,f64,f68,f72,f76,f80,f84,f90,f99,f120,f131,f138,f144,f147,f150])).
% 0.13/0.42  fof(f150,plain,(
% 0.13/0.42    spl4_2 | ~spl4_15 | ~spl4_22),
% 0.13/0.42    inference(avatar_contradiction_clause,[],[f149])).
% 0.13/0.42  fof(f149,plain,(
% 0.13/0.42    $false | (spl4_2 | ~spl4_15 | ~spl4_22)),
% 0.13/0.42    inference(subsumption_resolution,[],[f148,f98])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    r1_tarski(sK2,k2_relat_1(sK3)) | ~spl4_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f96])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    spl4_15 <=> r1_tarski(sK2,k2_relat_1(sK3))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.42  fof(f148,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k2_relat_1(sK3)) | (spl4_2 | ~spl4_22)),
% 0.21/0.42    inference(forward_demodulation,[],[f37,f137])).
% 0.21/0.42  fof(f137,plain,(
% 0.21/0.42    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl4_22),
% 0.21/0.42    inference(avatar_component_clause,[],[f135])).
% 0.21/0.42  fof(f135,plain,(
% 0.21/0.42    spl4_22 <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl4_2 <=> r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f147,plain,(
% 0.21/0.42    spl4_1 | ~spl4_21 | ~spl4_23),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f146])).
% 0.21/0.42  fof(f146,plain,(
% 0.21/0.42    $false | (spl4_1 | ~spl4_21 | ~spl4_23)),
% 0.21/0.42    inference(subsumption_resolution,[],[f145,f130])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    r1_tarski(sK2,k1_relat_1(sK3)) | ~spl4_21),
% 0.21/0.42    inference(avatar_component_clause,[],[f128])).
% 0.21/0.42  fof(f128,plain,(
% 0.21/0.42    spl4_21 <=> r1_tarski(sK2,k1_relat_1(sK3))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.42  fof(f145,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k1_relat_1(sK3)) | (spl4_1 | ~spl4_23)),
% 0.21/0.42    inference(superposition,[],[f33,f143])).
% 0.21/0.42  fof(f143,plain,(
% 0.21/0.42    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_23),
% 0.21/0.42    inference(avatar_component_clause,[],[f141])).
% 0.21/0.42  fof(f141,plain,(
% 0.21/0.42    spl4_23 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl4_1 <=> r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f144,plain,(
% 0.21/0.42    spl4_23 | ~spl4_4 | ~spl4_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f139,f82,f45,f141])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    spl4_13 <=> ! [X1,X0,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f139,plain,(
% 0.21/0.42    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | (~spl4_4 | ~spl4_13)),
% 0.21/0.42    inference(resolution,[],[f83,f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f45])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) ) | ~spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f82])).
% 0.21/0.42  fof(f138,plain,(
% 0.21/0.42    spl4_22 | ~spl4_4 | ~spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f133,f78,f45,f135])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl4_12 <=> ! [X1,X0,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | (~spl4_4 | ~spl4_12)),
% 0.21/0.42    inference(resolution,[],[f79,f47])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl4_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f78])).
% 0.21/0.42  fof(f131,plain,(
% 0.21/0.42    spl4_21 | ~spl4_3 | ~spl4_14 | ~spl4_19),
% 0.21/0.42    inference(avatar_split_clause,[],[f126,f118,f87,f40,f128])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl4_3 <=> r1_tarski(k6_relat_1(sK2),sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl4_14 <=> v1_relat_1(sK3)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    spl4_19 <=> ! [X1,X0] : (r1_tarski(X0,k1_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    r1_tarski(sK2,k1_relat_1(sK3)) | (~spl4_3 | ~spl4_14 | ~spl4_19)),
% 0.21/0.42    inference(subsumption_resolution,[],[f125,f89])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    v1_relat_1(sK3) | ~spl4_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f87])).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_19)),
% 0.21/0.42    inference(resolution,[],[f119,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    r1_tarski(k6_relat_1(sK2),sK3) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f40])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl4_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f118])).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    spl4_19 | ~spl4_6 | ~spl4_8 | ~spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f116,f70,f62,f54,f118])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl4_6 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl4_8 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl4_10 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(X1)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) ) | (~spl4_6 | ~spl4_8 | ~spl4_10)),
% 0.21/0.42    inference(forward_demodulation,[],[f114,f63])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl4_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f62])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(X1))) ) | (~spl4_6 | ~spl4_10)),
% 0.21/0.42    inference(resolution,[],[f71,f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f54])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) ) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f70])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    spl4_15 | ~spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f94,f87,f66,f58,f54,f40,f96])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl4_7 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl4_9 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    r1_tarski(sK2,k2_relat_1(sK3)) | (~spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_14)),
% 0.21/0.42    inference(forward_demodulation,[],[f93,f59])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)) | (~spl4_3 | ~spl4_6 | ~spl4_9 | ~spl4_14)),
% 0.21/0.42    inference(subsumption_resolution,[],[f92,f55])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)) | ~v1_relat_1(k6_relat_1(sK2)) | (~spl4_3 | ~spl4_9 | ~spl4_14)),
% 0.21/0.42    inference(subsumption_resolution,[],[f91,f89])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    r1_tarski(k2_relat_1(k6_relat_1(sK2)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(k6_relat_1(sK2)) | (~spl4_3 | ~spl4_9)),
% 0.21/0.42    inference(resolution,[],[f67,f42])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl4_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    spl4_14 | ~spl4_4 | ~spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f85,f74,f45,f87])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl4_11 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    v1_relat_1(sK3) | (~spl4_4 | ~spl4_11)),
% 0.21/0.42    inference(resolution,[],[f75,f47])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl4_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f74])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    spl4_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f82])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f78])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl4_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f74])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f70])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl4_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f66])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f62])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f58])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f54])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f45])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f40])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    r1_tarski(k6_relat_1(sK2),sK3)),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ~spl4_1 | ~spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f35,f31])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (29291)------------------------------
% 0.21/0.42  % (29291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (29291)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (29291)Memory used [KB]: 10618
% 0.21/0.42  % (29291)Time elapsed: 0.006 s
% 0.21/0.42  % (29291)------------------------------
% 0.21/0.42  % (29291)------------------------------
% 0.21/0.43  % (29285)Success in time 0.064 s
%------------------------------------------------------------------------------
