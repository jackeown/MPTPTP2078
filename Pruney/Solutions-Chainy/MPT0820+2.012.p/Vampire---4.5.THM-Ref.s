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
% DateTime   : Thu Dec  3 12:56:20 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 194 expanded)
%              Number of leaves         :   32 (  89 expanded)
%              Depth                    :    7
%              Number of atoms          :  303 ( 470 expanded)
%              Number of equality atoms :   26 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f55,f59,f65,f70,f74,f82,f86,f98,f104,f108,f113,f119,f125,f129,f135,f139,f145,f155,f161,f165])).

fof(f165,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | ~ spl3_13
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_13
    | spl3_24 ),
    inference(subsumption_resolution,[],[f163,f64])).

fof(f64,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f163,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_7
    | ~ spl3_13
    | spl3_24 ),
    inference(subsumption_resolution,[],[f162,f103])).

fof(f103,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_13
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f162,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_7
    | spl3_24 ),
    inference(resolution,[],[f160,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f160,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_24 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl3_24
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f161,plain,
    ( ~ spl3_24
    | spl3_2
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f156,f153,f48,f158])).

fof(f48,plain,
    ( spl3_2
  <=> r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f153,plain,
    ( spl3_23
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f156,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_2
    | ~ spl3_23 ),
    inference(resolution,[],[f154,f50])).

fof(f50,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f154,plain,
    ( ! [X0] :
        ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))
        | ~ r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( spl3_23
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f150,f143,f122,f153])).

fof(f122,plain,
    ( spl3_17
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f143,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1)))
        | ~ r1_tarski(k2_relat_1(sK2),X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0))) )
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(resolution,[],[f144,f124])).

fof(f124,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f122])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | ~ r1_tarski(k2_relat_1(sK2),X1)
        | r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( spl3_21
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f140,f137,f132,f143])).

fof(f132,plain,
    ( spl3_19
  <=> k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f137,plain,
    ( spl3_20
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1)))
        | ~ r1_tarski(k2_relat_1(sK2),X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(superposition,[],[f138,f134])).

fof(f134,plain,
    ( k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f132])).

fof(f138,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f41,f137])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f38,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f135,plain,
    ( spl3_19
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f130,f127,f62,f132])).

fof(f127,plain,
    ( spl3_18
  <=> ! [X0] :
        ( k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f130,plain,
    ( k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))
    | ~ spl3_5
    | ~ spl3_18 ),
    inference(resolution,[],[f128,f64])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f40,f127])).

fof(f40,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f27,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f125,plain,
    ( spl3_17
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f120,f116,f68,f122])).

fof(f68,plain,
    ( spl3_6
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f116,plain,
    ( spl3_16
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f120,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(superposition,[],[f69,f118])).

fof(f118,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f116])).

fof(f69,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f119,plain,
    ( spl3_16
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f114,f111,f95,f116])).

fof(f95,plain,
    ( spl3_12
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f111,plain,
    ( spl3_15
  <=> ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | sK2 = k7_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f114,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(resolution,[],[f112,f97])).

fof(f97,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | sK2 = k7_relat_1(sK2,X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f109,f106,f62,f111])).

fof(f106,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | sK2 = k7_relat_1(sK2,X0) )
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(resolution,[],[f107,f64])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k7_relat_1(X1,X0) = X1 )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f33,f106])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f104,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f99,f84,f43,f101])).

fof(f43,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f84,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f99,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f85,f45])).

fof(f45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f85,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f98,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f93,f80,f43,f95])).

fof(f80,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f93,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f81,f45])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f86,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f36,f84])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f82,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f70,plain,
    ( spl3_6
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f66,f62,f53,f68])).

fof(f53,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f66,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f64,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f65,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f60,f57,f43,f62])).

fof(f57,plain,
    ( spl3_4
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f60,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f58,f45])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f34,f57])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f55,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f30,f53])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f51,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f39,f48])).

fof(f39,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f26,f38])).

fof(f26,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

fof(f46,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f25,f43])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (3232)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.13/0.41  % (3232)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f166,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(avatar_sat_refutation,[],[f46,f51,f55,f59,f65,f70,f74,f82,f86,f98,f104,f108,f113,f119,f125,f129,f135,f139,f145,f155,f161,f165])).
% 0.13/0.41  fof(f165,plain,(
% 0.13/0.41    ~spl3_5 | ~spl3_7 | ~spl3_13 | spl3_24),
% 0.13/0.41    inference(avatar_contradiction_clause,[],[f164])).
% 0.13/0.41  fof(f164,plain,(
% 0.13/0.41    $false | (~spl3_5 | ~spl3_7 | ~spl3_13 | spl3_24)),
% 0.13/0.41    inference(subsumption_resolution,[],[f163,f64])).
% 0.13/0.41  fof(f64,plain,(
% 0.13/0.41    v1_relat_1(sK2) | ~spl3_5),
% 0.13/0.41    inference(avatar_component_clause,[],[f62])).
% 0.13/0.41  fof(f62,plain,(
% 0.13/0.41    spl3_5 <=> v1_relat_1(sK2)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.13/0.41  fof(f163,plain,(
% 0.13/0.41    ~v1_relat_1(sK2) | (~spl3_7 | ~spl3_13 | spl3_24)),
% 0.13/0.41    inference(subsumption_resolution,[],[f162,f103])).
% 0.13/0.41  fof(f103,plain,(
% 0.13/0.41    v5_relat_1(sK2,sK1) | ~spl3_13),
% 0.13/0.41    inference(avatar_component_clause,[],[f101])).
% 0.13/0.41  fof(f101,plain,(
% 0.13/0.41    spl3_13 <=> v5_relat_1(sK2,sK1)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.13/0.41  fof(f162,plain,(
% 0.13/0.41    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (~spl3_7 | spl3_24)),
% 0.13/0.41    inference(resolution,[],[f160,f73])).
% 0.13/0.41  fof(f73,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.13/0.41    inference(avatar_component_clause,[],[f72])).
% 0.13/0.41  fof(f72,plain,(
% 0.13/0.41    spl3_7 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.13/0.41  fof(f160,plain,(
% 0.13/0.41    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_24),
% 0.13/0.41    inference(avatar_component_clause,[],[f158])).
% 0.13/0.41  fof(f158,plain,(
% 0.13/0.41    spl3_24 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.13/0.41  fof(f161,plain,(
% 0.13/0.41    ~spl3_24 | spl3_2 | ~spl3_23),
% 0.13/0.41    inference(avatar_split_clause,[],[f156,f153,f48,f158])).
% 0.13/0.41  fof(f48,plain,(
% 0.13/0.41    spl3_2 <=> r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.13/0.41  fof(f153,plain,(
% 0.13/0.41    spl3_23 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0))))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.13/0.41  fof(f156,plain,(
% 0.13/0.41    ~r1_tarski(k2_relat_1(sK2),sK1) | (spl3_2 | ~spl3_23)),
% 0.13/0.41    inference(resolution,[],[f154,f50])).
% 0.13/0.41  fof(f50,plain,(
% 0.13/0.41    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) | spl3_2),
% 0.13/0.41    inference(avatar_component_clause,[],[f48])).
% 0.13/0.41  fof(f154,plain,(
% 0.13/0.41    ( ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0))) | ~r1_tarski(k2_relat_1(sK2),X0)) ) | ~spl3_23),
% 0.13/0.41    inference(avatar_component_clause,[],[f153])).
% 0.13/0.41  fof(f155,plain,(
% 0.13/0.41    spl3_23 | ~spl3_17 | ~spl3_21),
% 0.13/0.41    inference(avatar_split_clause,[],[f150,f143,f122,f153])).
% 0.13/0.41  fof(f122,plain,(
% 0.13/0.41    spl3_17 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.13/0.41  fof(f143,plain,(
% 0.13/0.41    spl3_21 <=> ! [X1,X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) | ~r1_tarski(k2_relat_1(sK2),X1) | ~r1_tarski(k1_relat_1(sK2),X0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.13/0.41  fof(f150,plain,(
% 0.13/0.41    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))) ) | (~spl3_17 | ~spl3_21)),
% 0.13/0.41    inference(resolution,[],[f144,f124])).
% 0.13/0.41  fof(f124,plain,(
% 0.13/0.41    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_17),
% 0.13/0.41    inference(avatar_component_clause,[],[f122])).
% 0.13/0.41  fof(f144,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK2),X0) | ~r1_tarski(k2_relat_1(sK2),X1) | r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1)))) ) | ~spl3_21),
% 0.13/0.41    inference(avatar_component_clause,[],[f143])).
% 0.13/0.41  fof(f145,plain,(
% 0.13/0.41    spl3_21 | ~spl3_19 | ~spl3_20),
% 0.13/0.41    inference(avatar_split_clause,[],[f140,f137,f132,f143])).
% 0.13/0.41  fof(f132,plain,(
% 0.13/0.41    spl3_19 <=> k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.13/0.41  fof(f137,plain,(
% 0.13/0.41    spl3_20 <=> ! [X1,X3,X0,X2] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.13/0.41  fof(f140,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) | ~r1_tarski(k2_relat_1(sK2),X1) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | (~spl3_19 | ~spl3_20)),
% 0.13/0.41    inference(superposition,[],[f138,f134])).
% 0.13/0.41  fof(f134,plain,(
% 0.13/0.41    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) | ~spl3_19),
% 0.13/0.41    inference(avatar_component_clause,[],[f132])).
% 0.13/0.41  fof(f138,plain,(
% 0.13/0.41    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) ) | ~spl3_20),
% 0.13/0.41    inference(avatar_component_clause,[],[f137])).
% 0.13/0.41  fof(f139,plain,(
% 0.13/0.41    spl3_20),
% 0.13/0.41    inference(avatar_split_clause,[],[f41,f137])).
% 0.13/0.41  fof(f41,plain,(
% 0.13/0.41    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f37,f38,f38])).
% 0.13/0.41  fof(f38,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.13/0.41    inference(definition_unfolding,[],[f28,f29])).
% 0.13/0.41  fof(f29,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f2])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.13/0.41  fof(f28,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.13/0.41  fof(f37,plain,(
% 0.13/0.41    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f21])).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.13/0.41    inference(flattening,[],[f20])).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.13/0.41    inference(ennf_transformation,[],[f1])).
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
% 0.13/0.41  fof(f135,plain,(
% 0.13/0.41    spl3_19 | ~spl3_5 | ~spl3_18),
% 0.13/0.41    inference(avatar_split_clause,[],[f130,f127,f62,f132])).
% 0.13/0.41  fof(f127,plain,(
% 0.13/0.41    spl3_18 <=> ! [X0] : (k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.13/0.41  fof(f130,plain,(
% 0.13/0.41    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) | (~spl3_5 | ~spl3_18)),
% 0.13/0.41    inference(resolution,[],[f128,f64])).
% 0.13/0.41  fof(f128,plain,(
% 0.13/0.41    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) ) | ~spl3_18),
% 0.13/0.41    inference(avatar_component_clause,[],[f127])).
% 0.13/0.41  fof(f129,plain,(
% 0.13/0.41    spl3_18),
% 0.13/0.41    inference(avatar_split_clause,[],[f40,f127])).
% 0.13/0.41  fof(f40,plain,(
% 0.13/0.41    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f27,f38])).
% 0.13/0.41  fof(f27,plain,(
% 0.13/0.41    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f13])).
% 0.13/0.41  fof(f13,plain,(
% 0.13/0.41    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.13/0.41    inference(ennf_transformation,[],[f5])).
% 0.13/0.41  fof(f5,axiom,(
% 0.13/0.41    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.41  fof(f125,plain,(
% 0.20/0.41    spl3_17 | ~spl3_6 | ~spl3_16),
% 0.20/0.41    inference(avatar_split_clause,[],[f120,f116,f68,f122])).
% 0.20/0.41  fof(f68,plain,(
% 0.20/0.41    spl3_6 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.41  fof(f116,plain,(
% 0.20/0.41    spl3_16 <=> sK2 = k7_relat_1(sK2,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.41  fof(f120,plain,(
% 0.20/0.41    r1_tarski(k1_relat_1(sK2),sK0) | (~spl3_6 | ~spl3_16)),
% 0.20/0.41    inference(superposition,[],[f69,f118])).
% 0.20/0.41  fof(f118,plain,(
% 0.20/0.41    sK2 = k7_relat_1(sK2,sK0) | ~spl3_16),
% 0.20/0.41    inference(avatar_component_clause,[],[f116])).
% 0.20/0.41  fof(f69,plain,(
% 0.20/0.41    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) ) | ~spl3_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f68])).
% 0.20/0.41  fof(f119,plain,(
% 0.20/0.41    spl3_16 | ~spl3_12 | ~spl3_15),
% 0.20/0.41    inference(avatar_split_clause,[],[f114,f111,f95,f116])).
% 0.20/0.41  fof(f95,plain,(
% 0.20/0.41    spl3_12 <=> v4_relat_1(sK2,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.41  fof(f111,plain,(
% 0.20/0.41    spl3_15 <=> ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.41  fof(f114,plain,(
% 0.20/0.41    sK2 = k7_relat_1(sK2,sK0) | (~spl3_12 | ~spl3_15)),
% 0.20/0.41    inference(resolution,[],[f112,f97])).
% 0.20/0.41  fof(f97,plain,(
% 0.20/0.41    v4_relat_1(sK2,sK0) | ~spl3_12),
% 0.20/0.41    inference(avatar_component_clause,[],[f95])).
% 0.20/0.41  fof(f112,plain,(
% 0.20/0.41    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) ) | ~spl3_15),
% 0.20/0.41    inference(avatar_component_clause,[],[f111])).
% 0.20/0.41  fof(f113,plain,(
% 0.20/0.41    spl3_15 | ~spl3_5 | ~spl3_14),
% 0.20/0.41    inference(avatar_split_clause,[],[f109,f106,f62,f111])).
% 0.20/0.41  fof(f106,plain,(
% 0.20/0.41    spl3_14 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.41  fof(f109,plain,(
% 0.20/0.41    ( ! [X0] : (~v4_relat_1(sK2,X0) | sK2 = k7_relat_1(sK2,X0)) ) | (~spl3_5 | ~spl3_14)),
% 0.20/0.41    inference(resolution,[],[f107,f64])).
% 0.20/0.41  fof(f107,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) ) | ~spl3_14),
% 0.20/0.41    inference(avatar_component_clause,[],[f106])).
% 0.20/0.41  fof(f108,plain,(
% 0.20/0.41    spl3_14),
% 0.20/0.41    inference(avatar_split_clause,[],[f33,f106])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.41    inference(flattening,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    spl3_13 | ~spl3_1 | ~spl3_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f99,f84,f43,f101])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    spl3_10 <=> ! [X1,X0,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    v5_relat_1(sK2,sK1) | (~spl3_1 | ~spl3_10)),
% 0.20/0.42    inference(resolution,[],[f85,f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f43])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) ) | ~spl3_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f84])).
% 0.20/0.42  fof(f98,plain,(
% 0.20/0.42    spl3_12 | ~spl3_1 | ~spl3_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f93,f80,f43,f95])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    spl3_9 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.42  fof(f93,plain,(
% 0.20/0.42    v4_relat_1(sK2,sK0) | (~spl3_1 | ~spl3_9)),
% 0.20/0.42    inference(resolution,[],[f81,f45])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl3_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f80])).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    spl3_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f36,f84])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    spl3_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f35,f80])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    spl3_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f31,f72])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(nnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    spl3_6 | ~spl3_3 | ~spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f66,f62,f53,f68])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl3_3 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) ) | (~spl3_3 | ~spl3_5)),
% 0.20/0.42    inference(resolution,[],[f64,f54])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) ) | ~spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f53])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    spl3_5 | ~spl3_1 | ~spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f60,f57,f43,f62])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl3_4 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    v1_relat_1(sK2) | (~spl3_1 | ~spl3_4)),
% 0.20/0.42    inference(resolution,[],[f58,f45])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f57])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f34,f57])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl3_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f30,f53])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ~spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f39,f48])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 0.20/0.42    inference(definition_unfolding,[],[f26,f38])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.20/0.42    inference(negated_conjecture,[],[f10])).
% 0.20/0.42  fof(f10,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f43])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.42    inference(cnf_transformation,[],[f23])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (3232)------------------------------
% 0.20/0.42  % (3232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (3232)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (3232)Memory used [KB]: 6140
% 0.20/0.42  % (3232)Time elapsed: 0.008 s
% 0.20/0.42  % (3232)------------------------------
% 0.20/0.42  % (3232)------------------------------
% 0.20/0.42  % (3224)Success in time 0.06 s
%------------------------------------------------------------------------------
