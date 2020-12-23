%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 178 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :    7
%              Number of atoms          :  336 ( 590 expanded)
%              Number of equality atoms :   65 ( 112 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f65,f73,f77,f81,f85,f89,f93,f99,f129,f135,f147,f154,f161,f169,f180,f188,f197])).

fof(f197,plain,
    ( ~ spl4_8
    | spl4_22
    | ~ spl4_25
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl4_8
    | spl4_22
    | ~ spl4_25
    | spl4_28 ),
    inference(subsumption_resolution,[],[f195,f160])).

fof(f160,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_25
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f195,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_8
    | spl4_22
    | spl4_28 ),
    inference(subsumption_resolution,[],[f194,f140])).

fof(f140,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_22
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f194,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_8
    | spl4_28 ),
    inference(resolution,[],[f187,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f187,plain,
    ( ~ r2_hidden(sK3(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl4_28
  <=> r2_hidden(sK3(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f188,plain,
    ( ~ spl4_28
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f182,f165,f152,f185])).

fof(f152,plain,
    ( spl4_24
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f165,plain,
    ( spl4_26
  <=> m1_subset_1(sK3(sK1,k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f182,plain,
    ( ~ r2_hidden(sK3(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl4_24
    | ~ spl4_26 ),
    inference(resolution,[],[f167,f153])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f152])).

fof(f167,plain,
    ( m1_subset_1(sK3(sK1,k2_relat_1(sK2)),sK1)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f165])).

fof(f180,plain,
    ( ~ spl4_6
    | ~ spl4_14
    | spl4_21
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_14
    | spl4_21
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f178,f98])).

fof(f98,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f178,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_6
    | spl4_21
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f172,f134])).

fof(f134,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_21
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f172,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(trivial_inequality_removal,[],[f171])).

fof(f171,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_22 ),
    inference(superposition,[],[f64,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f64,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_6
  <=> ! [X0] :
        ( k1_xboole_0 = k1_relat_1(X0)
        | k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f169,plain,
    ( spl4_26
    | spl4_22
    | ~ spl4_9
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f162,f158,f75,f139,f165])).

fof(f75,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( m1_subset_1(sK3(X0,X1),X0)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f162,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | m1_subset_1(sK3(sK1,k2_relat_1(sK2)),sK1)
    | ~ spl4_9
    | ~ spl4_25 ),
    inference(resolution,[],[f160,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k1_xboole_0 = X1
        | m1_subset_1(sK3(X0,X1),X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f161,plain,
    ( spl4_25
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f156,f144,f91,f48,f158])).

fof(f48,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f91,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f144,plain,
    ( spl4_23
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f156,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f155,f146])).

fof(f146,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f144])).

fof(f155,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(resolution,[],[f92,f50])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f154,plain,
    ( spl4_24
    | ~ spl4_1
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f149,f144,f39,f152])).

fof(f39,plain,
    ( spl4_1
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl4_1
    | ~ spl4_23 ),
    inference(superposition,[],[f40,f146])).

fof(f40,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f147,plain,
    ( spl4_23
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f136,f87,f48,f144])).

fof(f87,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f136,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(resolution,[],[f88,f50])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f135,plain,
    ( ~ spl4_21
    | spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f130,f126,f43,f132])).

fof(f43,plain,
    ( spl4_2
  <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f126,plain,
    ( spl4_20
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f130,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_2
    | ~ spl4_20 ),
    inference(superposition,[],[f45,f128])).

fof(f128,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f126])).

fof(f45,plain,
    ( k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f129,plain,
    ( spl4_20
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f124,f83,f48,f126])).

fof(f83,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f124,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(resolution,[],[f84,f50])).

fof(f84,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f99,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f94,f79,f48,f96])).

fof(f79,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f94,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f80,f50])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f93,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f37,f91])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f89,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f36,f87])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f85,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f35,f83])).

fof(f35,plain,(
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

fof(f81,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f77,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f73,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f33,f71])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f51,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f46,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f28,f43])).

fof(f28,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f29,f39])).

fof(f29,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:01:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (10821)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (10821)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f198,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f41,f46,f51,f65,f73,f77,f81,f85,f89,f93,f99,f129,f135,f147,f154,f161,f169,f180,f188,f197])).
% 0.21/0.43  fof(f197,plain,(
% 0.21/0.43    ~spl4_8 | spl4_22 | ~spl4_25 | spl4_28),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f196])).
% 0.21/0.43  fof(f196,plain,(
% 0.21/0.43    $false | (~spl4_8 | spl4_22 | ~spl4_25 | spl4_28)),
% 0.21/0.43    inference(subsumption_resolution,[],[f195,f160])).
% 0.21/0.43  fof(f160,plain,(
% 0.21/0.43    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl4_25),
% 0.21/0.43    inference(avatar_component_clause,[],[f158])).
% 0.21/0.43  fof(f158,plain,(
% 0.21/0.43    spl4_25 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.43  fof(f195,plain,(
% 0.21/0.43    ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl4_8 | spl4_22 | spl4_28)),
% 0.21/0.43    inference(subsumption_resolution,[],[f194,f140])).
% 0.21/0.43  fof(f140,plain,(
% 0.21/0.43    k1_xboole_0 != k2_relat_1(sK2) | spl4_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f139])).
% 0.21/0.43  fof(f139,plain,(
% 0.21/0.43    spl4_22 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.43  fof(f194,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(sK2) | ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl4_8 | spl4_28)),
% 0.21/0.43    inference(resolution,[],[f187,f72])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl4_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f71])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl4_8 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.43  fof(f187,plain,(
% 0.21/0.43    ~r2_hidden(sK3(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | spl4_28),
% 0.21/0.43    inference(avatar_component_clause,[],[f185])).
% 0.21/0.43  fof(f185,plain,(
% 0.21/0.43    spl4_28 <=> r2_hidden(sK3(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.43  fof(f188,plain,(
% 0.21/0.43    ~spl4_28 | ~spl4_24 | ~spl4_26),
% 0.21/0.43    inference(avatar_split_clause,[],[f182,f165,f152,f185])).
% 0.21/0.43  fof(f152,plain,(
% 0.21/0.43    spl4_24 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | ~m1_subset_1(X0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.43  fof(f165,plain,(
% 0.21/0.43    spl4_26 <=> m1_subset_1(sK3(sK1,k2_relat_1(sK2)),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.43  fof(f182,plain,(
% 0.21/0.43    ~r2_hidden(sK3(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | (~spl4_24 | ~spl4_26)),
% 0.21/0.43    inference(resolution,[],[f167,f153])).
% 0.21/0.43  fof(f153,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl4_24),
% 0.21/0.43    inference(avatar_component_clause,[],[f152])).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    m1_subset_1(sK3(sK1,k2_relat_1(sK2)),sK1) | ~spl4_26),
% 0.21/0.43    inference(avatar_component_clause,[],[f165])).
% 0.21/0.43  fof(f180,plain,(
% 0.21/0.43    ~spl4_6 | ~spl4_14 | spl4_21 | ~spl4_22),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.43  fof(f179,plain,(
% 0.21/0.43    $false | (~spl4_6 | ~spl4_14 | spl4_21 | ~spl4_22)),
% 0.21/0.43    inference(subsumption_resolution,[],[f178,f98])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    v1_relat_1(sK2) | ~spl4_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f96])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    spl4_14 <=> v1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.43  fof(f178,plain,(
% 0.21/0.43    ~v1_relat_1(sK2) | (~spl4_6 | spl4_21 | ~spl4_22)),
% 0.21/0.43    inference(subsumption_resolution,[],[f172,f134])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    k1_xboole_0 != k1_relat_1(sK2) | spl4_21),
% 0.21/0.43    inference(avatar_component_clause,[],[f132])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    spl4_21 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl4_6 | ~spl4_22)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f171])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl4_6 | ~spl4_22)),
% 0.21/0.43    inference(superposition,[],[f64,f141])).
% 0.21/0.43  fof(f141,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f139])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl4_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl4_6 <=> ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.43  fof(f169,plain,(
% 0.21/0.43    spl4_26 | spl4_22 | ~spl4_9 | ~spl4_25),
% 0.21/0.43    inference(avatar_split_clause,[],[f162,f158,f75,f139,f165])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl4_9 <=> ! [X1,X0] : (m1_subset_1(sK3(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.43  fof(f162,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(sK2) | m1_subset_1(sK3(sK1,k2_relat_1(sK2)),sK1) | (~spl4_9 | ~spl4_25)),
% 0.21/0.43    inference(resolution,[],[f160,f76])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | m1_subset_1(sK3(X0,X1),X0)) ) | ~spl4_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f75])).
% 0.21/0.43  fof(f161,plain,(
% 0.21/0.43    spl4_25 | ~spl4_3 | ~spl4_13 | ~spl4_23),
% 0.21/0.43    inference(avatar_split_clause,[],[f156,f144,f91,f48,f158])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    spl4_13 <=> ! [X1,X0,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.43  fof(f144,plain,(
% 0.21/0.43    spl4_23 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.43  fof(f156,plain,(
% 0.21/0.43    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | (~spl4_3 | ~spl4_13 | ~spl4_23)),
% 0.21/0.43    inference(forward_demodulation,[],[f155,f146])).
% 0.21/0.43  fof(f146,plain,(
% 0.21/0.43    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl4_23),
% 0.21/0.43    inference(avatar_component_clause,[],[f144])).
% 0.21/0.43  fof(f155,plain,(
% 0.21/0.43    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | (~spl4_3 | ~spl4_13)),
% 0.21/0.43    inference(resolution,[],[f92,f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f48])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) ) | ~spl4_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f91])).
% 0.21/0.43  fof(f154,plain,(
% 0.21/0.43    spl4_24 | ~spl4_1 | ~spl4_23),
% 0.21/0.43    inference(avatar_split_clause,[],[f149,f144,f39,f152])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl4_1 <=> ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f149,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | ~m1_subset_1(X0,sK1)) ) | (~spl4_1 | ~spl4_23)),
% 0.21/0.43    inference(superposition,[],[f40,f146])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) ) | ~spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f39])).
% 0.21/0.43  fof(f147,plain,(
% 0.21/0.43    spl4_23 | ~spl4_3 | ~spl4_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f136,f87,f48,f144])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl4_12 <=> ! [X1,X0,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.43  fof(f136,plain,(
% 0.21/0.43    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | (~spl4_3 | ~spl4_12)),
% 0.21/0.43    inference(resolution,[],[f88,f50])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl4_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f87])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    ~spl4_21 | spl4_2 | ~spl4_20),
% 0.21/0.43    inference(avatar_split_clause,[],[f130,f126,f43,f132])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl4_2 <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    spl4_20 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.43  fof(f130,plain,(
% 0.21/0.43    k1_xboole_0 != k1_relat_1(sK2) | (spl4_2 | ~spl4_20)),
% 0.21/0.43    inference(superposition,[],[f45,f128])).
% 0.21/0.43  fof(f128,plain,(
% 0.21/0.43    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl4_20),
% 0.21/0.43    inference(avatar_component_clause,[],[f126])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) | spl4_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f43])).
% 0.21/0.43  fof(f129,plain,(
% 0.21/0.43    spl4_20 | ~spl4_3 | ~spl4_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f124,f83,f48,f126])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl4_11 <=> ! [X1,X0,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | (~spl4_3 | ~spl4_11)),
% 0.21/0.43    inference(resolution,[],[f84,f50])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) ) | ~spl4_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f83])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    spl4_14 | ~spl4_3 | ~spl4_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f94,f79,f48,f96])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    spl4_10 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    v1_relat_1(sK2) | (~spl4_3 | ~spl4_10)),
% 0.21/0.43    inference(resolution,[],[f80,f50])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl4_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f79])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    spl4_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f37,f91])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    spl4_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f36,f87])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    spl4_11),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f83])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    spl4_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f34,f79])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    spl4_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f75])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1] : ((r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl4_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f33,f71])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl4_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f31,f63])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl4_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f48])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.43    inference(flattening,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ~spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f43])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f39])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (10821)------------------------------
% 0.21/0.43  % (10821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (10821)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (10821)Memory used [KB]: 10618
% 0.21/0.43  % (10821)Time elapsed: 0.009 s
% 0.21/0.43  % (10821)------------------------------
% 0.21/0.43  % (10821)------------------------------
% 0.21/0.43  % (10817)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (10815)Success in time 0.068 s
%------------------------------------------------------------------------------
