%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:01 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 168 expanded)
%              Number of leaves         :   29 (  78 expanded)
%              Depth                    :    7
%              Number of atoms          :  284 ( 455 expanded)
%              Number of equality atoms :   33 (  58 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f61,f65,f69,f77,f81,f85,f91,f98,f110,f117,f123,f128,f134,f140,f162,f167,f170])).

fof(f170,plain,
    ( spl4_1
    | ~ spl4_25
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl4_1
    | ~ spl4_25
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f168,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_25
  <=> k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f168,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,sK1)
    | spl4_1
    | ~ spl4_26 ),
    inference(superposition,[],[f38,f166])).

fof(f166,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_26
  <=> ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f38,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_1
  <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f167,plain,
    ( spl4_26
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f163,f83,f46,f165])).

fof(f46,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f83,plain,
    ( spl4_12
  <=> ! [X1,X3,X0,X2] :
        ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f163,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(resolution,[],[f84,f48])).

fof(f48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f84,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f162,plain,
    ( spl4_25
    | ~ spl4_13
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f156,f138,f88,f159])).

fof(f88,plain,
    ( spl4_13
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f138,plain,
    ( spl4_21
  <=> ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK3,X0)
        | ~ r1_xboole_0(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f156,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK1)
    | ~ spl4_13
    | ~ spl4_21 ),
    inference(resolution,[],[f139,f90])).

fof(f90,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k1_xboole_0 = k7_relat_1(sK3,X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl4_21
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f135,f132,f126,f138])).

fof(f126,plain,
    ( spl4_19
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | r1_xboole_0(X0,k1_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f132,plain,
    ( spl4_20
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,k1_relat_1(sK3))
        | k1_xboole_0 = k7_relat_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f135,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK3,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(resolution,[],[f133,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,k1_relat_1(sK3))
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f126])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_relat_1(sK3))
        | k1_xboole_0 = k7_relat_1(sK3,X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f130,f95,f51,f132])).

fof(f51,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f95,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_relat_1(sK3))
        | k1_xboole_0 = k7_relat_1(sK3,X0) )
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(resolution,[],[f52,f97])).

fof(f97,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_xboole_0(X1,k1_relat_1(X0))
        | k7_relat_1(X0,X1) = k1_xboole_0 )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f128,plain,
    ( spl4_19
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f124,f121,f63,f126])).

fof(f63,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f121,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | r1_xboole_0(k1_relat_1(sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | r1_xboole_0(X0,k1_relat_1(sK3)) )
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(resolution,[],[f122,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f122,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_relat_1(sK3),X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( spl4_18
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f119,f114,f79,f121])).

fof(f79,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f114,plain,
    ( spl4_17
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | r1_xboole_0(k1_relat_1(sK3),X0) )
    | ~ spl4_11
    | ~ spl4_17 ),
    inference(resolution,[],[f80,f116])).

fof(f116,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f114])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f117,plain,
    ( spl4_17
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f112,f107,f95,f59,f114])).

fof(f59,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f107,plain,
    ( spl4_16
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f112,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f111,f97])).

fof(f111,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(resolution,[],[f109,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X1,X0)
        | r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f109,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f110,plain,
    ( spl4_16
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f105,f75,f46,f107])).

fof(f75,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f105,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f98,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f93,f67,f46,f95])).

fof(f67,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f93,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(resolution,[],[f68,f48])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f91,plain,
    ( spl4_13
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f86,f63,f41,f88])).

fof(f41,plain,
    ( spl4_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f86,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f85,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f34,f83])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f81,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f77,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f69,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f65,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f61,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f53,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f49,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20])).

% (1061)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
        & r1_xboole_0(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
   => ( k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

fof(f44,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f36])).

fof(f25,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (1066)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.41  % (1067)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.13/0.41  % (1068)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.13/0.41  % (1066)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f171,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f61,f65,f69,f77,f81,f85,f91,f98,f110,f117,f123,f128,f134,f140,f162,f167,f170])).
% 0.13/0.41  fof(f170,plain,(
% 0.13/0.41    spl4_1 | ~spl4_25 | ~spl4_26),
% 0.13/0.41    inference(avatar_contradiction_clause,[],[f169])).
% 0.13/0.41  fof(f169,plain,(
% 0.13/0.41    $false | (spl4_1 | ~spl4_25 | ~spl4_26)),
% 0.13/0.41    inference(subsumption_resolution,[],[f168,f161])).
% 0.13/0.41  fof(f161,plain,(
% 0.13/0.41    k1_xboole_0 = k7_relat_1(sK3,sK1) | ~spl4_25),
% 0.13/0.41    inference(avatar_component_clause,[],[f159])).
% 0.13/0.41  fof(f159,plain,(
% 0.13/0.41    spl4_25 <=> k1_xboole_0 = k7_relat_1(sK3,sK1)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.13/0.41  fof(f168,plain,(
% 0.13/0.41    k1_xboole_0 != k7_relat_1(sK3,sK1) | (spl4_1 | ~spl4_26)),
% 0.13/0.41    inference(superposition,[],[f38,f166])).
% 0.13/0.41  fof(f166,plain,(
% 0.13/0.41    ( ! [X0] : (k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)) ) | ~spl4_26),
% 0.13/0.41    inference(avatar_component_clause,[],[f165])).
% 0.13/0.41  fof(f165,plain,(
% 0.13/0.41    spl4_26 <=> ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.13/0.41  fof(f38,plain,(
% 0.13/0.41    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) | spl4_1),
% 0.13/0.41    inference(avatar_component_clause,[],[f36])).
% 0.13/0.41  fof(f36,plain,(
% 0.13/0.41    spl4_1 <=> k1_xboole_0 = k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.13/0.41  fof(f167,plain,(
% 0.13/0.41    spl4_26 | ~spl4_3 | ~spl4_12),
% 0.13/0.41    inference(avatar_split_clause,[],[f163,f83,f46,f165])).
% 0.13/0.41  fof(f46,plain,(
% 0.13/0.41    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.13/0.41  fof(f83,plain,(
% 0.13/0.41    spl4_12 <=> ! [X1,X3,X0,X2] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.13/0.41  fof(f163,plain,(
% 0.13/0.41    ( ! [X0] : (k7_relat_1(sK3,X0) = k5_relset_1(sK2,sK0,sK3,X0)) ) | (~spl4_3 | ~spl4_12)),
% 0.13/0.41    inference(resolution,[],[f84,f48])).
% 0.13/0.41  fof(f48,plain,(
% 0.13/0.41    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl4_3),
% 0.13/0.41    inference(avatar_component_clause,[],[f46])).
% 0.13/0.41  fof(f84,plain,(
% 0.13/0.41    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) ) | ~spl4_12),
% 0.13/0.41    inference(avatar_component_clause,[],[f83])).
% 0.13/0.41  fof(f162,plain,(
% 0.13/0.41    spl4_25 | ~spl4_13 | ~spl4_21),
% 0.13/0.41    inference(avatar_split_clause,[],[f156,f138,f88,f159])).
% 0.13/0.41  fof(f88,plain,(
% 0.13/0.41    spl4_13 <=> r1_xboole_0(sK2,sK1)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.13/0.41  fof(f138,plain,(
% 0.13/0.41    spl4_21 <=> ! [X0] : (k1_xboole_0 = k7_relat_1(sK3,X0) | ~r1_xboole_0(sK2,X0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.13/0.41  fof(f156,plain,(
% 0.13/0.41    k1_xboole_0 = k7_relat_1(sK3,sK1) | (~spl4_13 | ~spl4_21)),
% 0.13/0.41    inference(resolution,[],[f139,f90])).
% 0.13/0.41  fof(f90,plain,(
% 0.13/0.41    r1_xboole_0(sK2,sK1) | ~spl4_13),
% 0.13/0.41    inference(avatar_component_clause,[],[f88])).
% 0.13/0.41  fof(f139,plain,(
% 0.13/0.41    ( ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl4_21),
% 0.13/0.41    inference(avatar_component_clause,[],[f138])).
% 0.13/0.41  fof(f140,plain,(
% 0.13/0.41    spl4_21 | ~spl4_19 | ~spl4_20),
% 0.13/0.41    inference(avatar_split_clause,[],[f135,f132,f126,f138])).
% 0.13/0.41  fof(f126,plain,(
% 0.13/0.41    spl4_19 <=> ! [X0] : (~r1_xboole_0(sK2,X0) | r1_xboole_0(X0,k1_relat_1(sK3)))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.13/0.41  fof(f132,plain,(
% 0.13/0.41    spl4_20 <=> ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK3)) | k1_xboole_0 = k7_relat_1(sK3,X0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.13/0.41  fof(f135,plain,(
% 0.13/0.41    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK3,X0) | ~r1_xboole_0(sK2,X0)) ) | (~spl4_19 | ~spl4_20)),
% 0.13/0.41    inference(resolution,[],[f133,f127])).
% 0.13/0.41  fof(f127,plain,(
% 0.13/0.41    ( ! [X0] : (r1_xboole_0(X0,k1_relat_1(sK3)) | ~r1_xboole_0(sK2,X0)) ) | ~spl4_19),
% 0.13/0.41    inference(avatar_component_clause,[],[f126])).
% 0.13/0.41  fof(f133,plain,(
% 0.13/0.41    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK3)) | k1_xboole_0 = k7_relat_1(sK3,X0)) ) | ~spl4_20),
% 0.13/0.41    inference(avatar_component_clause,[],[f132])).
% 0.13/0.41  fof(f134,plain,(
% 0.13/0.41    spl4_20 | ~spl4_4 | ~spl4_14),
% 0.13/0.41    inference(avatar_split_clause,[],[f130,f95,f51,f132])).
% 0.13/0.41  fof(f51,plain,(
% 0.13/0.41    spl4_4 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.13/0.41  fof(f95,plain,(
% 0.13/0.41    spl4_14 <=> v1_relat_1(sK3)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.13/0.41  fof(f130,plain,(
% 0.13/0.41    ( ! [X0] : (~r1_xboole_0(X0,k1_relat_1(sK3)) | k1_xboole_0 = k7_relat_1(sK3,X0)) ) | (~spl4_4 | ~spl4_14)),
% 0.13/0.41    inference(resolution,[],[f52,f97])).
% 0.13/0.41  fof(f97,plain,(
% 0.13/0.41    v1_relat_1(sK3) | ~spl4_14),
% 0.13/0.41    inference(avatar_component_clause,[],[f95])).
% 0.13/0.41  fof(f52,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(X1,k1_relat_1(X0)) | k7_relat_1(X0,X1) = k1_xboole_0) ) | ~spl4_4),
% 0.13/0.41    inference(avatar_component_clause,[],[f51])).
% 0.13/0.41  fof(f128,plain,(
% 0.13/0.41    spl4_19 | ~spl4_7 | ~spl4_18),
% 0.13/0.41    inference(avatar_split_clause,[],[f124,f121,f63,f126])).
% 0.13/0.41  fof(f63,plain,(
% 0.13/0.41    spl4_7 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.13/0.41  fof(f121,plain,(
% 0.13/0.41    spl4_18 <=> ! [X0] : (~r1_xboole_0(sK2,X0) | r1_xboole_0(k1_relat_1(sK3),X0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.13/0.41  fof(f124,plain,(
% 0.13/0.41    ( ! [X0] : (~r1_xboole_0(sK2,X0) | r1_xboole_0(X0,k1_relat_1(sK3))) ) | (~spl4_7 | ~spl4_18)),
% 0.13/0.41    inference(resolution,[],[f122,f64])).
% 0.13/0.41  fof(f64,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_7),
% 0.13/0.41    inference(avatar_component_clause,[],[f63])).
% 0.13/0.41  fof(f122,plain,(
% 0.13/0.41    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK3),X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl4_18),
% 0.13/0.41    inference(avatar_component_clause,[],[f121])).
% 0.13/0.41  fof(f123,plain,(
% 0.13/0.41    spl4_18 | ~spl4_11 | ~spl4_17),
% 0.13/0.41    inference(avatar_split_clause,[],[f119,f114,f79,f121])).
% 0.13/0.41  fof(f79,plain,(
% 0.13/0.41    spl4_11 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.13/0.41  fof(f114,plain,(
% 0.13/0.41    spl4_17 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.13/0.41  fof(f119,plain,(
% 0.13/0.41    ( ! [X0] : (~r1_xboole_0(sK2,X0) | r1_xboole_0(k1_relat_1(sK3),X0)) ) | (~spl4_11 | ~spl4_17)),
% 0.13/0.41    inference(resolution,[],[f80,f116])).
% 0.13/0.41  fof(f116,plain,(
% 0.13/0.41    r1_tarski(k1_relat_1(sK3),sK2) | ~spl4_17),
% 0.13/0.41    inference(avatar_component_clause,[],[f114])).
% 0.13/0.41  fof(f80,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl4_11),
% 0.13/0.41    inference(avatar_component_clause,[],[f79])).
% 0.13/0.41  fof(f117,plain,(
% 0.13/0.41    spl4_17 | ~spl4_6 | ~spl4_14 | ~spl4_16),
% 0.13/0.41    inference(avatar_split_clause,[],[f112,f107,f95,f59,f114])).
% 0.13/0.41  fof(f59,plain,(
% 0.13/0.41    spl4_6 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.13/0.41  fof(f107,plain,(
% 0.13/0.41    spl4_16 <=> v4_relat_1(sK3,sK2)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.13/0.41  fof(f112,plain,(
% 0.13/0.41    r1_tarski(k1_relat_1(sK3),sK2) | (~spl4_6 | ~spl4_14 | ~spl4_16)),
% 0.13/0.41    inference(subsumption_resolution,[],[f111,f97])).
% 0.13/0.41  fof(f111,plain,(
% 0.13/0.41    r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | (~spl4_6 | ~spl4_16)),
% 0.13/0.41    inference(resolution,[],[f109,f60])).
% 0.13/0.41  fof(f60,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl4_6),
% 0.13/0.41    inference(avatar_component_clause,[],[f59])).
% 0.13/0.41  fof(f109,plain,(
% 0.13/0.41    v4_relat_1(sK3,sK2) | ~spl4_16),
% 0.13/0.41    inference(avatar_component_clause,[],[f107])).
% 0.13/0.41  fof(f110,plain,(
% 0.13/0.41    spl4_16 | ~spl4_3 | ~spl4_10),
% 0.13/0.41    inference(avatar_split_clause,[],[f105,f75,f46,f107])).
% 0.13/0.41  fof(f75,plain,(
% 0.13/0.41    spl4_10 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.13/0.41  fof(f105,plain,(
% 0.13/0.41    v4_relat_1(sK3,sK2) | (~spl4_3 | ~spl4_10)),
% 0.13/0.41    inference(resolution,[],[f76,f48])).
% 0.13/0.41  fof(f76,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl4_10),
% 0.13/0.41    inference(avatar_component_clause,[],[f75])).
% 0.13/0.41  fof(f98,plain,(
% 0.13/0.41    spl4_14 | ~spl4_3 | ~spl4_8),
% 0.13/0.41    inference(avatar_split_clause,[],[f93,f67,f46,f95])).
% 0.13/0.41  fof(f67,plain,(
% 0.13/0.41    spl4_8 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.13/0.41  fof(f93,plain,(
% 0.13/0.41    v1_relat_1(sK3) | (~spl4_3 | ~spl4_8)),
% 0.13/0.41    inference(resolution,[],[f68,f48])).
% 0.13/0.41  fof(f68,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl4_8),
% 0.13/0.41    inference(avatar_component_clause,[],[f67])).
% 0.13/0.41  fof(f91,plain,(
% 0.13/0.41    spl4_13 | ~spl4_2 | ~spl4_7),
% 0.13/0.41    inference(avatar_split_clause,[],[f86,f63,f41,f88])).
% 0.13/0.41  fof(f41,plain,(
% 0.13/0.41    spl4_2 <=> r1_xboole_0(sK1,sK2)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.13/0.41  fof(f86,plain,(
% 0.13/0.41    r1_xboole_0(sK2,sK1) | (~spl4_2 | ~spl4_7)),
% 0.13/0.41    inference(resolution,[],[f64,f43])).
% 0.13/0.41  fof(f43,plain,(
% 0.13/0.41    r1_xboole_0(sK1,sK2) | ~spl4_2),
% 0.13/0.41    inference(avatar_component_clause,[],[f41])).
% 0.13/0.42  fof(f85,plain,(
% 0.13/0.42    spl4_12),
% 0.13/0.42    inference(avatar_split_clause,[],[f34,f83])).
% 0.13/0.42  fof(f34,plain,(
% 0.13/0.42    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f19])).
% 0.13/0.42  fof(f19,plain,(
% 0.13/0.42    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.42    inference(ennf_transformation,[],[f7])).
% 0.13/0.42  fof(f7,axiom,(
% 0.13/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.13/0.42  fof(f81,plain,(
% 0.13/0.42    spl4_11),
% 0.13/0.42    inference(avatar_split_clause,[],[f33,f79])).
% 0.13/0.42  fof(f33,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f18])).
% 0.13/0.42  fof(f18,plain,(
% 0.13/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.13/0.42    inference(flattening,[],[f17])).
% 0.13/0.42  fof(f17,plain,(
% 0.13/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.13/0.42    inference(ennf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.13/0.42  fof(f77,plain,(
% 0.13/0.42    spl4_10),
% 0.13/0.42    inference(avatar_split_clause,[],[f31,f75])).
% 0.13/0.42  fof(f31,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f16])).
% 0.13/0.42  fof(f16,plain,(
% 0.13/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.42    inference(ennf_transformation,[],[f6])).
% 0.13/0.42  fof(f6,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.13/0.42  fof(f69,plain,(
% 0.13/0.42    spl4_8),
% 0.13/0.42    inference(avatar_split_clause,[],[f30,f67])).
% 0.13/0.42  fof(f30,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f15])).
% 0.13/0.42  fof(f15,plain,(
% 0.13/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.42    inference(ennf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.13/0.42  fof(f65,plain,(
% 0.13/0.42    spl4_7),
% 0.13/0.42    inference(avatar_split_clause,[],[f29,f63])).
% 0.13/0.42  fof(f29,plain,(
% 0.13/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f14])).
% 0.13/0.42  fof(f14,plain,(
% 0.13/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.13/0.42  fof(f61,plain,(
% 0.13/0.42    spl4_6),
% 0.13/0.42    inference(avatar_split_clause,[],[f27,f59])).
% 0.13/0.42  fof(f27,plain,(
% 0.13/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f22])).
% 0.13/0.42  fof(f22,plain,(
% 0.13/0.42    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(nnf_transformation,[],[f13])).
% 0.13/0.42  fof(f13,plain,(
% 0.13/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f3])).
% 0.13/0.42  fof(f3,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.13/0.42  fof(f53,plain,(
% 0.13/0.42    spl4_4),
% 0.13/0.42    inference(avatar_split_clause,[],[f26,f51])).
% 0.13/0.42  fof(f26,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f12])).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.13/0.42    inference(ennf_transformation,[],[f4])).
% 0.13/0.42  fof(f4,axiom,(
% 0.13/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.13/0.42  fof(f49,plain,(
% 0.13/0.42    spl4_3),
% 0.13/0.42    inference(avatar_split_clause,[],[f23,f46])).
% 0.13/0.42  fof(f23,plain,(
% 0.13/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.13/0.42    inference(cnf_transformation,[],[f21])).
% 0.13/0.42  fof(f21,plain,(
% 0.13/0.42    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.13/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f20])).
% 0.20/0.42  % (1061)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) => (k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.42    inference(flattening,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.20/0.42    inference(negated_conjecture,[],[f8])).
% 0.20/0.42  fof(f8,conjecture,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    spl4_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f41])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    r1_xboole_0(sK1,sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ~spl4_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f36])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (1066)------------------------------
% 0.20/0.42  % (1066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (1066)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (1066)Memory used [KB]: 10618
% 0.20/0.42  % (1066)Time elapsed: 0.006 s
% 0.20/0.42  % (1066)------------------------------
% 0.20/0.42  % (1066)------------------------------
% 0.20/0.43  % (1060)Success in time 0.071 s
%------------------------------------------------------------------------------
