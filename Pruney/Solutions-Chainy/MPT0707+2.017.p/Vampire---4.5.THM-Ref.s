%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:28 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 168 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :    6
%              Number of atoms          :  262 ( 402 expanded)
%              Number of equality atoms :   71 ( 117 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f49,f53,f57,f61,f65,f69,f73,f77,f85,f92,f97,f103,f109,f116,f122,f129,f142,f143,f155])).

fof(f155,plain,
    ( ~ spl2_8
    | ~ spl2_21
    | spl2_22 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_21
    | spl2_22 ),
    inference(subsumption_resolution,[],[f147,f141])).

fof(f141,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl2_22
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f147,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_8
    | ~ spl2_21 ),
    inference(superposition,[],[f64,f136])).

fof(f136,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl2_21
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f64,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f143,plain,
    ( spl2_21
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f132,f127,f113,f134])).

fof(f113,plain,
    ( spl2_18
  <=> sK1 = k9_relat_1(k6_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f127,plain,
    ( spl2_20
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f132,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(superposition,[],[f115,f128])).

fof(f128,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f127])).

fof(f115,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK1),sK0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f142,plain,
    ( ~ spl2_22
    | spl2_1
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f131,f127,f33,f139])).

fof(f33,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f131,plain,
    ( sK1 != k3_xboole_0(sK0,sK1)
    | spl2_1
    | ~ spl2_20 ),
    inference(superposition,[],[f35,f128])).

fof(f35,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f129,plain,
    ( spl2_20
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f125,f120,f67,f51,f47,f127])).

fof(f47,plain,
    ( spl2_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f51,plain,
    ( spl2_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f120,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k9_relat_1(X0,X1) = k2_relat_1(k5_relat_1(k6_relat_1(X1),X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f125,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f124,f52])).

fof(f52,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f124,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f123,f68])).

fof(f68,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f123,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))
    | ~ spl2_4
    | ~ spl2_19 ),
    inference(resolution,[],[f121,f48])).

fof(f48,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k9_relat_1(X0,X1) = k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl2_19
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f118,f59,f51,f47,f120])).

fof(f59,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( k9_relat_1(X0,X1) = k2_relat_1(k5_relat_1(k6_relat_1(X1),X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f117,f52])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1))) )
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(resolution,[],[f60,f48])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f116,plain,
    ( spl2_18
    | ~ spl2_5
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f111,f106,f95,f51,f113])).

fof(f95,plain,
    ( spl2_15
  <=> ! [X1,X0] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f106,plain,
    ( spl2_17
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f111,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK1),sK0)
    | ~ spl2_5
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f110,f52])).

fof(f110,plain,
    ( k9_relat_1(k6_relat_1(sK1),sK0) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(superposition,[],[f96,f108])).

fof(f108,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f106])).

fof(f96,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f109,plain,
    ( spl2_17
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f104,f101,f89,f106])).

fof(f89,plain,
    ( spl2_14
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f101,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f104,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0)
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(resolution,[],[f102,f91])).

fof(f91,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl2_16
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f99,f75,f55,f47,f101])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f75,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f98,f56])).

fof(f56,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1 )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f75])).

fof(f97,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f93,f71,f47,f95])).

fof(f71,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f93,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(resolution,[],[f72,f48])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f92,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f86,f83,f38,f89])).

fof(f38,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f83,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f86,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(resolution,[],[f84,f40])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f30,f83])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f77,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f73,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f69,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f61,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f49,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 15:45:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.43  % (20490)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.23/0.43  % (20492)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.23/0.43  % (20491)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.23/0.43  % (20490)Refutation found. Thanks to Tanya!
% 0.23/0.43  % SZS status Theorem for theBenchmark
% 0.23/0.43  % SZS output start Proof for theBenchmark
% 0.23/0.43  fof(f156,plain,(
% 0.23/0.43    $false),
% 0.23/0.43    inference(avatar_sat_refutation,[],[f36,f41,f49,f53,f57,f61,f65,f69,f73,f77,f85,f92,f97,f103,f109,f116,f122,f129,f142,f143,f155])).
% 0.23/0.43  fof(f155,plain,(
% 0.23/0.43    ~spl2_8 | ~spl2_21 | spl2_22),
% 0.23/0.43    inference(avatar_contradiction_clause,[],[f154])).
% 0.23/0.43  fof(f154,plain,(
% 0.23/0.43    $false | (~spl2_8 | ~spl2_21 | spl2_22)),
% 0.23/0.43    inference(subsumption_resolution,[],[f147,f141])).
% 0.23/0.43  fof(f141,plain,(
% 0.23/0.43    sK1 != k3_xboole_0(sK0,sK1) | spl2_22),
% 0.23/0.43    inference(avatar_component_clause,[],[f139])).
% 0.23/0.43  fof(f139,plain,(
% 0.23/0.43    spl2_22 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.23/0.43  fof(f147,plain,(
% 0.23/0.43    sK1 = k3_xboole_0(sK0,sK1) | (~spl2_8 | ~spl2_21)),
% 0.23/0.43    inference(superposition,[],[f64,f136])).
% 0.23/0.43  fof(f136,plain,(
% 0.23/0.43    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_21),
% 0.23/0.43    inference(avatar_component_clause,[],[f134])).
% 0.23/0.43  fof(f134,plain,(
% 0.23/0.43    spl2_21 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.23/0.43  fof(f64,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_8),
% 0.23/0.43    inference(avatar_component_clause,[],[f63])).
% 0.23/0.43  fof(f63,plain,(
% 0.23/0.43    spl2_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.23/0.43  fof(f143,plain,(
% 0.23/0.43    spl2_21 | ~spl2_18 | ~spl2_20),
% 0.23/0.43    inference(avatar_split_clause,[],[f132,f127,f113,f134])).
% 0.23/0.43  fof(f113,plain,(
% 0.23/0.43    spl2_18 <=> sK1 = k9_relat_1(k6_relat_1(sK1),sK0)),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.23/0.43  fof(f127,plain,(
% 0.23/0.43    spl2_20 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.23/0.43  fof(f132,plain,(
% 0.23/0.43    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_18 | ~spl2_20)),
% 0.23/0.43    inference(superposition,[],[f115,f128])).
% 0.23/0.43  fof(f128,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_20),
% 0.23/0.43    inference(avatar_component_clause,[],[f127])).
% 0.23/0.43  fof(f115,plain,(
% 0.23/0.43    sK1 = k9_relat_1(k6_relat_1(sK1),sK0) | ~spl2_18),
% 0.23/0.43    inference(avatar_component_clause,[],[f113])).
% 0.23/0.43  fof(f142,plain,(
% 0.23/0.43    ~spl2_22 | spl2_1 | ~spl2_20),
% 0.23/0.43    inference(avatar_split_clause,[],[f131,f127,f33,f139])).
% 0.23/0.43  fof(f33,plain,(
% 0.23/0.43    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.43  fof(f131,plain,(
% 0.23/0.43    sK1 != k3_xboole_0(sK0,sK1) | (spl2_1 | ~spl2_20)),
% 0.23/0.43    inference(superposition,[],[f35,f128])).
% 0.23/0.43  fof(f35,plain,(
% 0.23/0.43    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.23/0.43    inference(avatar_component_clause,[],[f33])).
% 0.23/0.43  fof(f129,plain,(
% 0.23/0.43    spl2_20 | ~spl2_4 | ~spl2_5 | ~spl2_9 | ~spl2_19),
% 0.23/0.43    inference(avatar_split_clause,[],[f125,f120,f67,f51,f47,f127])).
% 0.23/0.43  fof(f47,plain,(
% 0.23/0.43    spl2_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.43  fof(f51,plain,(
% 0.23/0.43    spl2_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.23/0.43  fof(f67,plain,(
% 0.23/0.43    spl2_9 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.23/0.43  fof(f120,plain,(
% 0.23/0.43    spl2_19 <=> ! [X1,X0] : (k9_relat_1(X0,X1) = k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) | ~v1_relat_1(X0))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.23/0.43  fof(f125,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_4 | ~spl2_5 | ~spl2_9 | ~spl2_19)),
% 0.23/0.43    inference(forward_demodulation,[],[f124,f52])).
% 0.23/0.43  fof(f52,plain,(
% 0.23/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.23/0.43    inference(avatar_component_clause,[],[f51])).
% 0.23/0.43  fof(f124,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))) ) | (~spl2_4 | ~spl2_9 | ~spl2_19)),
% 0.23/0.43    inference(forward_demodulation,[],[f123,f68])).
% 0.23/0.43  fof(f68,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_9),
% 0.23/0.43    inference(avatar_component_clause,[],[f67])).
% 0.23/0.43  fof(f123,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) ) | (~spl2_4 | ~spl2_19)),
% 0.23/0.43    inference(resolution,[],[f121,f48])).
% 0.23/0.43  fof(f48,plain,(
% 0.23/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.23/0.43    inference(avatar_component_clause,[],[f47])).
% 0.23/0.43  fof(f121,plain,(
% 0.23/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(X0,X1) = k2_relat_1(k5_relat_1(k6_relat_1(X1),X0))) ) | ~spl2_19),
% 0.23/0.43    inference(avatar_component_clause,[],[f120])).
% 0.23/0.43  fof(f122,plain,(
% 0.23/0.43    spl2_19 | ~spl2_4 | ~spl2_5 | ~spl2_7),
% 0.23/0.43    inference(avatar_split_clause,[],[f118,f59,f51,f47,f120])).
% 0.23/0.43  fof(f59,plain,(
% 0.23/0.43    spl2_7 <=> ! [X1,X0] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.23/0.43  fof(f118,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k9_relat_1(X0,X1) = k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) | ~v1_relat_1(X0)) ) | (~spl2_4 | ~spl2_5 | ~spl2_7)),
% 0.23/0.43    inference(forward_demodulation,[],[f117,f52])).
% 0.23/0.43  fof(f117,plain,(
% 0.23/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(X0,k2_relat_1(k6_relat_1(X1)))) ) | (~spl2_4 | ~spl2_7)),
% 0.23/0.43    inference(resolution,[],[f60,f48])).
% 0.23/0.43  fof(f60,plain,(
% 0.23/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) ) | ~spl2_7),
% 0.23/0.43    inference(avatar_component_clause,[],[f59])).
% 0.23/0.43  fof(f116,plain,(
% 0.23/0.43    spl2_18 | ~spl2_5 | ~spl2_15 | ~spl2_17),
% 0.23/0.43    inference(avatar_split_clause,[],[f111,f106,f95,f51,f113])).
% 0.23/0.43  fof(f95,plain,(
% 0.23/0.43    spl2_15 <=> ! [X1,X0] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.23/0.43  fof(f106,plain,(
% 0.23/0.43    spl2_17 <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0)),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.23/0.43  fof(f111,plain,(
% 0.23/0.43    sK1 = k9_relat_1(k6_relat_1(sK1),sK0) | (~spl2_5 | ~spl2_15 | ~spl2_17)),
% 0.23/0.43    inference(forward_demodulation,[],[f110,f52])).
% 0.23/0.43  fof(f110,plain,(
% 0.23/0.43    k9_relat_1(k6_relat_1(sK1),sK0) = k2_relat_1(k6_relat_1(sK1)) | (~spl2_15 | ~spl2_17)),
% 0.23/0.43    inference(superposition,[],[f96,f108])).
% 0.23/0.43  fof(f108,plain,(
% 0.23/0.43    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0) | ~spl2_17),
% 0.23/0.43    inference(avatar_component_clause,[],[f106])).
% 0.23/0.43  fof(f96,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_15),
% 0.23/0.43    inference(avatar_component_clause,[],[f95])).
% 0.23/0.43  fof(f109,plain,(
% 0.23/0.43    spl2_17 | ~spl2_14 | ~spl2_16),
% 0.23/0.43    inference(avatar_split_clause,[],[f104,f101,f89,f106])).
% 0.23/0.43  fof(f89,plain,(
% 0.23/0.43    spl2_14 <=> r1_tarski(sK1,sK0)),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.23/0.43  fof(f101,plain,(
% 0.23/0.43    spl2_16 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.23/0.43  fof(f104,plain,(
% 0.23/0.43    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK0) | (~spl2_14 | ~spl2_16)),
% 0.23/0.43    inference(resolution,[],[f102,f91])).
% 0.23/0.43  fof(f91,plain,(
% 0.23/0.43    r1_tarski(sK1,sK0) | ~spl2_14),
% 0.23/0.43    inference(avatar_component_clause,[],[f89])).
% 0.23/0.43  fof(f102,plain,(
% 0.23/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_16),
% 0.23/0.43    inference(avatar_component_clause,[],[f101])).
% 0.23/0.43  fof(f103,plain,(
% 0.23/0.43    spl2_16 | ~spl2_4 | ~spl2_6 | ~spl2_11),
% 0.23/0.43    inference(avatar_split_clause,[],[f99,f75,f55,f47,f101])).
% 0.23/0.43  fof(f55,plain,(
% 0.23/0.43    spl2_6 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.23/0.43  fof(f75,plain,(
% 0.23/0.43    spl2_11 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.23/0.43  fof(f99,plain,(
% 0.23/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_4 | ~spl2_6 | ~spl2_11)),
% 0.23/0.43    inference(forward_demodulation,[],[f98,f56])).
% 0.23/0.43  fof(f56,plain,(
% 0.23/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_6),
% 0.23/0.43    inference(avatar_component_clause,[],[f55])).
% 0.23/0.43  fof(f98,plain,(
% 0.23/0.43    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_4 | ~spl2_11)),
% 0.23/0.43    inference(resolution,[],[f76,f48])).
% 0.23/0.43  fof(f76,plain,(
% 0.23/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) ) | ~spl2_11),
% 0.23/0.43    inference(avatar_component_clause,[],[f75])).
% 0.23/0.43  fof(f97,plain,(
% 0.23/0.43    spl2_15 | ~spl2_4 | ~spl2_10),
% 0.23/0.43    inference(avatar_split_clause,[],[f93,f71,f47,f95])).
% 0.23/0.43  fof(f71,plain,(
% 0.23/0.43    spl2_10 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.23/0.43  fof(f93,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_4 | ~spl2_10)),
% 0.23/0.43    inference(resolution,[],[f72,f48])).
% 0.23/0.43  fof(f72,plain,(
% 0.23/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_10),
% 0.23/0.43    inference(avatar_component_clause,[],[f71])).
% 0.23/0.43  fof(f92,plain,(
% 0.23/0.43    spl2_14 | ~spl2_2 | ~spl2_13),
% 0.23/0.43    inference(avatar_split_clause,[],[f86,f83,f38,f89])).
% 0.23/0.43  fof(f38,plain,(
% 0.23/0.43    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.43  fof(f83,plain,(
% 0.23/0.43    spl2_13 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.23/0.43  fof(f86,plain,(
% 0.23/0.43    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_13)),
% 0.23/0.43    inference(resolution,[],[f84,f40])).
% 0.23/0.43  fof(f40,plain,(
% 0.23/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.23/0.43    inference(avatar_component_clause,[],[f38])).
% 0.23/0.43  fof(f84,plain,(
% 0.23/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.23/0.43    inference(avatar_component_clause,[],[f83])).
% 0.23/0.43  fof(f85,plain,(
% 0.23/0.43    spl2_13),
% 0.23/0.43    inference(avatar_split_clause,[],[f30,f83])).
% 0.23/0.43  fof(f30,plain,(
% 0.23/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.23/0.43    inference(cnf_transformation,[],[f18])).
% 0.23/0.43  fof(f18,plain,(
% 0.23/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.43    inference(nnf_transformation,[],[f2])).
% 0.23/0.43  fof(f2,axiom,(
% 0.23/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.43  fof(f77,plain,(
% 0.23/0.43    spl2_11),
% 0.23/0.43    inference(avatar_split_clause,[],[f29,f75])).
% 0.23/0.43  fof(f29,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f15])).
% 0.23/0.43  fof(f15,plain,(
% 0.23/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.43    inference(flattening,[],[f14])).
% 0.23/0.43  fof(f14,plain,(
% 0.23/0.43    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.43    inference(ennf_transformation,[],[f6])).
% 0.23/0.43  fof(f6,axiom,(
% 0.23/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.23/0.43  fof(f73,plain,(
% 0.23/0.43    spl2_10),
% 0.23/0.43    inference(avatar_split_clause,[],[f28,f71])).
% 0.23/0.43  fof(f28,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f13])).
% 0.23/0.43  fof(f13,plain,(
% 0.23/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.43    inference(ennf_transformation,[],[f3])).
% 0.23/0.43  fof(f3,axiom,(
% 0.23/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.23/0.43  fof(f69,plain,(
% 0.23/0.43    spl2_9),
% 0.23/0.43    inference(avatar_split_clause,[],[f27,f67])).
% 0.23/0.43  fof(f27,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.23/0.43    inference(cnf_transformation,[],[f8])).
% 0.23/0.43  fof(f8,axiom,(
% 0.23/0.43    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.23/0.43  fof(f65,plain,(
% 0.23/0.43    spl2_8),
% 0.23/0.43    inference(avatar_split_clause,[],[f26,f63])).
% 0.23/0.43  fof(f26,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f1])).
% 0.23/0.43  fof(f1,axiom,(
% 0.23/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.43  fof(f61,plain,(
% 0.23/0.43    spl2_7),
% 0.23/0.43    inference(avatar_split_clause,[],[f25,f59])).
% 0.23/0.43  fof(f25,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f12])).
% 0.23/0.43  fof(f12,plain,(
% 0.23/0.43    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.43    inference(ennf_transformation,[],[f4])).
% 0.23/0.43  fof(f4,axiom,(
% 0.23/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.23/0.43  fof(f57,plain,(
% 0.23/0.43    spl2_6),
% 0.23/0.43    inference(avatar_split_clause,[],[f23,f55])).
% 0.23/0.43  fof(f23,plain,(
% 0.23/0.43    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.43    inference(cnf_transformation,[],[f5])).
% 0.23/0.43  fof(f5,axiom,(
% 0.23/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.23/0.43  fof(f53,plain,(
% 0.23/0.43    spl2_5),
% 0.23/0.43    inference(avatar_split_clause,[],[f24,f51])).
% 0.23/0.43  fof(f24,plain,(
% 0.23/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.43    inference(cnf_transformation,[],[f5])).
% 0.23/0.43  fof(f49,plain,(
% 0.23/0.43    spl2_4),
% 0.23/0.43    inference(avatar_split_clause,[],[f21,f47])).
% 0.23/0.43  fof(f21,plain,(
% 0.23/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.43    inference(cnf_transformation,[],[f7])).
% 0.23/0.43  fof(f7,axiom,(
% 0.23/0.43    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.23/0.43  fof(f41,plain,(
% 0.23/0.43    spl2_2),
% 0.23/0.43    inference(avatar_split_clause,[],[f19,f38])).
% 0.23/0.43  fof(f19,plain,(
% 0.23/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.43    inference(cnf_transformation,[],[f17])).
% 0.23/0.43  fof(f17,plain,(
% 0.23/0.43    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16])).
% 0.23/0.43  fof(f16,plain,(
% 0.23/0.43    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.23/0.43    introduced(choice_axiom,[])).
% 0.23/0.43  fof(f11,plain,(
% 0.23/0.43    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.43    inference(ennf_transformation,[],[f10])).
% 0.23/0.43  fof(f10,negated_conjecture,(
% 0.23/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.23/0.43    inference(negated_conjecture,[],[f9])).
% 0.23/0.43  fof(f9,conjecture,(
% 0.23/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.23/0.43  fof(f36,plain,(
% 0.23/0.43    ~spl2_1),
% 0.23/0.43    inference(avatar_split_clause,[],[f20,f33])).
% 0.23/0.43  fof(f20,plain,(
% 0.23/0.43    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.23/0.43    inference(cnf_transformation,[],[f17])).
% 0.23/0.43  % SZS output end Proof for theBenchmark
% 0.23/0.43  % (20490)------------------------------
% 0.23/0.43  % (20490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.43  % (20490)Termination reason: Refutation
% 0.23/0.43  
% 0.23/0.43  % (20490)Memory used [KB]: 10618
% 0.23/0.43  % (20490)Time elapsed: 0.009 s
% 0.23/0.43  % (20490)------------------------------
% 0.23/0.43  % (20490)------------------------------
% 0.23/0.44  % (20484)Success in time 0.066 s
%------------------------------------------------------------------------------
