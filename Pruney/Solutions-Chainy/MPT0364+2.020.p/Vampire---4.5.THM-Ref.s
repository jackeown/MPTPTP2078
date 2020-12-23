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
% DateTime   : Thu Dec  3 12:45:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 240 expanded)
%              Number of leaves         :   32 ( 117 expanded)
%              Depth                    :    8
%              Number of atoms          :  352 ( 715 expanded)
%              Number of equality atoms :   36 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f40,f45,f50,f54,f58,f62,f66,f70,f74,f82,f87,f98,f104,f108,f112,f118,f125,f131,f142,f148,f175,f188,f217,f239,f259])).

fof(f259,plain,
    ( spl3_2
    | ~ spl3_14
    | ~ spl3_26
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl3_2
    | ~ spl3_14
    | ~ spl3_26
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f257,f238])).

fof(f238,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl3_34
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f257,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_2
    | ~ spl3_14
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f256,f38])).

fof(f38,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f256,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl3_14
    | ~ spl3_26 ),
    inference(resolution,[],[f187,f96])).

fof(f96,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_14
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(sK0,sK2))
        | r1_tarski(X0,sK2)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_26
  <=> ! [X0] :
        ( r1_tarski(X0,sK2)
        | ~ r1_xboole_0(X0,k4_xboole_0(sK0,sK2))
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f239,plain,
    ( spl3_34
    | ~ spl3_5
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f226,f213,f52,f236])).

fof(f52,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f213,plain,
    ( spl3_30
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f226,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5
    | ~ spl3_30 ),
    inference(superposition,[],[f53,f215])).

fof(f215,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f213])).

fof(f53,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f217,plain,
    ( spl3_30
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f210,f145,f128,f213])).

fof(f128,plain,
    ( spl3_18
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f145,plain,
    ( spl3_20
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f210,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_18
    | ~ spl3_20 ),
    inference(superposition,[],[f147,f130])).

fof(f130,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f128])).

fof(f147,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f145])).

fof(f188,plain,
    ( spl3_26
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f182,f171,f72,f186])).

fof(f72,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f171,plain,
    ( spl3_24
  <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f182,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK2)
        | ~ r1_xboole_0(X0,k4_xboole_0(sK0,sK2))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_10
    | ~ spl3_24 ),
    inference(superposition,[],[f73,f173])).

fof(f173,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f171])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f175,plain,
    ( spl3_24
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f168,f139,f115,f171])).

fof(f115,plain,
    ( spl3_16
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f139,plain,
    ( spl3_19
  <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f168,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(superposition,[],[f141,f117])).

fof(f117,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f115])).

fof(f141,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f139])).

fof(f148,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f143,f84,f64,f47,f145])).

fof(f47,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f64,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f84,plain,
    ( spl3_12
  <=> k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f143,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f133,f86])).

fof(f86,plain,
    ( k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f133,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f65,f49])).

fof(f49,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f142,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f137,f79,f64,f42,f139])).

fof(f42,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( spl3_11
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f137,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f132,f81])).

fof(f81,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f132,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f131,plain,
    ( spl3_18
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f126,f122,f60,f128])).

fof(f60,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f122,plain,
    ( spl3_17
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f126,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(resolution,[],[f124,f61])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f124,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f122])).

fof(f125,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f120,f84,f56,f47,f122])).

fof(f56,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f120,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f119,f49])).

fof(f119,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(superposition,[],[f57,f86])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f118,plain,
    ( spl3_16
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f113,f101,f60,f115])).

fof(f101,plain,
    ( spl3_15
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f113,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(resolution,[],[f103,f61])).

fof(f103,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f112,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f109,f79,f32,f95])).

fof(f32,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f109,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f33,f81])).

fof(f33,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f108,plain,
    ( ~ spl3_2
    | ~ spl3_9
    | spl3_14 ),
    inference(avatar_split_clause,[],[f105,f95,f68,f36])).

fof(f68,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f105,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl3_9
    | spl3_14 ),
    inference(resolution,[],[f97,f69])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f97,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f95])).

fof(f104,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f99,f79,f56,f42,f101])).

fof(f99,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f93,f44])).

fof(f93,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f57,f81])).

fof(f98,plain,
    ( ~ spl3_14
    | spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f92,f79,f32,f95])).

fof(f92,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_1
    | ~ spl3_11 ),
    inference(superposition,[],[f34,f81])).

fof(f34,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f87,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f76,f60,f47,f84])).

fof(f76,plain,
    ( k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f61,f49])).

fof(f82,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f75,f60,f42,f79])).

fof(f75,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f61,f44])).

fof(f74,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f70,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f66,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f62,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f58,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f54,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & ( r1_tarski(sK1,sK2)
      | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & ( r1_tarski(sK1,X2)
            | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & ( r1_tarski(sK1,X2)
          | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & ( r1_tarski(sK1,sK2)
        | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f23,f36,f32])).

fof(f23,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f36,f32])).

fof(f24,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (18727)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (18726)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (18722)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (18728)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (18726)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f260,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f39,f40,f45,f50,f54,f58,f62,f66,f70,f74,f82,f87,f98,f104,f108,f112,f118,f125,f131,f142,f148,f175,f188,f217,f239,f259])).
% 0.22/0.44  fof(f259,plain,(
% 0.22/0.44    spl3_2 | ~spl3_14 | ~spl3_26 | ~spl3_34),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f258])).
% 0.22/0.44  fof(f258,plain,(
% 0.22/0.44    $false | (spl3_2 | ~spl3_14 | ~spl3_26 | ~spl3_34)),
% 0.22/0.44    inference(subsumption_resolution,[],[f257,f238])).
% 0.22/0.44  fof(f238,plain,(
% 0.22/0.44    r1_tarski(sK1,sK0) | ~spl3_34),
% 0.22/0.44    inference(avatar_component_clause,[],[f236])).
% 0.22/0.44  fof(f236,plain,(
% 0.22/0.44    spl3_34 <=> r1_tarski(sK1,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.44  fof(f257,plain,(
% 0.22/0.44    ~r1_tarski(sK1,sK0) | (spl3_2 | ~spl3_14 | ~spl3_26)),
% 0.22/0.44    inference(subsumption_resolution,[],[f256,f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ~r1_tarski(sK1,sK2) | spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f256,plain,(
% 0.22/0.44    r1_tarski(sK1,sK2) | ~r1_tarski(sK1,sK0) | (~spl3_14 | ~spl3_26)),
% 0.22/0.44    inference(resolution,[],[f187,f96])).
% 0.22/0.44  fof(f96,plain,(
% 0.22/0.44    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f95])).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    spl3_14 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.44  fof(f187,plain,(
% 0.22/0.44    ( ! [X0] : (~r1_xboole_0(X0,k4_xboole_0(sK0,sK2)) | r1_tarski(X0,sK2) | ~r1_tarski(X0,sK0)) ) | ~spl3_26),
% 0.22/0.44    inference(avatar_component_clause,[],[f186])).
% 0.22/0.44  fof(f186,plain,(
% 0.22/0.44    spl3_26 <=> ! [X0] : (r1_tarski(X0,sK2) | ~r1_xboole_0(X0,k4_xboole_0(sK0,sK2)) | ~r1_tarski(X0,sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.44  fof(f239,plain,(
% 0.22/0.44    spl3_34 | ~spl3_5 | ~spl3_30),
% 0.22/0.44    inference(avatar_split_clause,[],[f226,f213,f52,f236])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl3_5 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f213,plain,(
% 0.22/0.44    spl3_30 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.44  fof(f226,plain,(
% 0.22/0.44    r1_tarski(sK1,sK0) | (~spl3_5 | ~spl3_30)),
% 0.22/0.44    inference(superposition,[],[f53,f215])).
% 0.22/0.44  fof(f215,plain,(
% 0.22/0.44    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_30),
% 0.22/0.44    inference(avatar_component_clause,[],[f213])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f52])).
% 0.22/0.44  fof(f217,plain,(
% 0.22/0.44    spl3_30 | ~spl3_18 | ~spl3_20),
% 0.22/0.44    inference(avatar_split_clause,[],[f210,f145,f128,f213])).
% 0.22/0.44  fof(f128,plain,(
% 0.22/0.44    spl3_18 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.44  fof(f145,plain,(
% 0.22/0.44    spl3_20 <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.44  fof(f210,plain,(
% 0.22/0.44    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_18 | ~spl3_20)),
% 0.22/0.44    inference(superposition,[],[f147,f130])).
% 0.22/0.44  fof(f130,plain,(
% 0.22/0.44    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_18),
% 0.22/0.44    inference(avatar_component_clause,[],[f128])).
% 0.22/0.44  fof(f147,plain,(
% 0.22/0.44    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_20),
% 0.22/0.44    inference(avatar_component_clause,[],[f145])).
% 0.22/0.44  fof(f188,plain,(
% 0.22/0.44    spl3_26 | ~spl3_10 | ~spl3_24),
% 0.22/0.44    inference(avatar_split_clause,[],[f182,f171,f72,f186])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    spl3_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.44  fof(f171,plain,(
% 0.22/0.44    spl3_24 <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.44  fof(f182,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(X0,sK2) | ~r1_xboole_0(X0,k4_xboole_0(sK0,sK2)) | ~r1_tarski(X0,sK0)) ) | (~spl3_10 | ~spl3_24)),
% 0.22/0.44    inference(superposition,[],[f73,f173])).
% 0.22/0.44  fof(f173,plain,(
% 0.22/0.44    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_24),
% 0.22/0.44    inference(avatar_component_clause,[],[f171])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f72])).
% 0.22/0.44  fof(f175,plain,(
% 0.22/0.44    spl3_24 | ~spl3_16 | ~spl3_19),
% 0.22/0.44    inference(avatar_split_clause,[],[f168,f139,f115,f171])).
% 0.22/0.44  fof(f115,plain,(
% 0.22/0.44    spl3_16 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.44  fof(f139,plain,(
% 0.22/0.44    spl3_19 <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.44  fof(f168,plain,(
% 0.22/0.44    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_16 | ~spl3_19)),
% 0.22/0.44    inference(superposition,[],[f141,f117])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_16),
% 0.22/0.44    inference(avatar_component_clause,[],[f115])).
% 0.22/0.44  fof(f141,plain,(
% 0.22/0.44    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_19),
% 0.22/0.44    inference(avatar_component_clause,[],[f139])).
% 0.22/0.44  fof(f148,plain,(
% 0.22/0.44    spl3_20 | ~spl3_4 | ~spl3_8 | ~spl3_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f143,f84,f64,f47,f145])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    spl3_8 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    spl3_12 <=> k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.44  fof(f143,plain,(
% 0.22/0.44    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_4 | ~spl3_8 | ~spl3_12)),
% 0.22/0.44    inference(forward_demodulation,[],[f133,f86])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1) | ~spl3_12),
% 0.22/0.44    inference(avatar_component_clause,[],[f84])).
% 0.22/0.44  fof(f133,plain,(
% 0.22/0.44    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | (~spl3_4 | ~spl3_8)),
% 0.22/0.44    inference(resolution,[],[f65,f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f47])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl3_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f64])).
% 0.22/0.44  fof(f142,plain,(
% 0.22/0.44    spl3_19 | ~spl3_3 | ~spl3_8 | ~spl3_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f137,f79,f64,f42,f139])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    spl3_11 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.44  fof(f137,plain,(
% 0.22/0.44    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_3 | ~spl3_8 | ~spl3_11)),
% 0.22/0.44    inference(forward_demodulation,[],[f132,f81])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_11),
% 0.22/0.44    inference(avatar_component_clause,[],[f79])).
% 0.22/0.44  fof(f132,plain,(
% 0.22/0.44    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | (~spl3_3 | ~spl3_8)),
% 0.22/0.44    inference(resolution,[],[f65,f44])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f42])).
% 0.22/0.44  fof(f131,plain,(
% 0.22/0.44    spl3_18 | ~spl3_7 | ~spl3_17),
% 0.22/0.44    inference(avatar_split_clause,[],[f126,f122,f60,f128])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    spl3_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f122,plain,(
% 0.22/0.44    spl3_17 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.44  fof(f126,plain,(
% 0.22/0.44    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_7 | ~spl3_17)),
% 0.22/0.44    inference(resolution,[],[f124,f61])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f60])).
% 0.22/0.44  fof(f124,plain,(
% 0.22/0.44    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_17),
% 0.22/0.44    inference(avatar_component_clause,[],[f122])).
% 0.22/0.44  fof(f125,plain,(
% 0.22/0.44    spl3_17 | ~spl3_4 | ~spl3_6 | ~spl3_12),
% 0.22/0.44    inference(avatar_split_clause,[],[f120,f84,f56,f47,f122])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl3_6 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f120,plain,(
% 0.22/0.44    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_4 | ~spl3_6 | ~spl3_12)),
% 0.22/0.44    inference(subsumption_resolution,[],[f119,f49])).
% 0.22/0.44  fof(f119,plain,(
% 0.22/0.44    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_6 | ~spl3_12)),
% 0.22/0.44    inference(superposition,[],[f57,f86])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f56])).
% 0.22/0.44  fof(f118,plain,(
% 0.22/0.44    spl3_16 | ~spl3_7 | ~spl3_15),
% 0.22/0.44    inference(avatar_split_clause,[],[f113,f101,f60,f115])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    spl3_15 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.44  fof(f113,plain,(
% 0.22/0.44    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_7 | ~spl3_15)),
% 0.22/0.44    inference(resolution,[],[f103,f61])).
% 0.22/0.44  fof(f103,plain,(
% 0.22/0.44    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_15),
% 0.22/0.44    inference(avatar_component_clause,[],[f101])).
% 0.22/0.44  fof(f112,plain,(
% 0.22/0.44    spl3_14 | ~spl3_1 | ~spl3_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f109,f79,f32,f95])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    spl3_1 <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f109,plain,(
% 0.22/0.44    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_1 | ~spl3_11)),
% 0.22/0.44    inference(forward_demodulation,[],[f33,f81])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f32])).
% 0.22/0.44  fof(f108,plain,(
% 0.22/0.44    ~spl3_2 | ~spl3_9 | spl3_14),
% 0.22/0.44    inference(avatar_split_clause,[],[f105,f95,f68,f36])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl3_9 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    ~r1_tarski(sK1,sK2) | (~spl3_9 | spl3_14)),
% 0.22/0.44    inference(resolution,[],[f97,f69])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f68])).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_14),
% 0.22/0.44    inference(avatar_component_clause,[],[f95])).
% 0.22/0.44  fof(f104,plain,(
% 0.22/0.44    spl3_15 | ~spl3_3 | ~spl3_6 | ~spl3_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f99,f79,f56,f42,f101])).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_3 | ~spl3_6 | ~spl3_11)),
% 0.22/0.44    inference(subsumption_resolution,[],[f93,f44])).
% 0.22/0.44  fof(f93,plain,(
% 0.22/0.44    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl3_6 | ~spl3_11)),
% 0.22/0.44    inference(superposition,[],[f57,f81])).
% 0.22/0.44  fof(f98,plain,(
% 0.22/0.44    ~spl3_14 | spl3_1 | ~spl3_11),
% 0.22/0.44    inference(avatar_split_clause,[],[f92,f79,f32,f95])).
% 0.22/0.44  fof(f92,plain,(
% 0.22/0.44    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (spl3_1 | ~spl3_11)),
% 0.22/0.44    inference(superposition,[],[f34,f81])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f32])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    spl3_12 | ~spl3_4 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f76,f60,f47,f84])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1) | (~spl3_4 | ~spl3_7)),
% 0.22/0.44    inference(resolution,[],[f61,f49])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    spl3_11 | ~spl3_3 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f75,f60,f42,f79])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | (~spl3_3 | ~spl3_7)),
% 0.22/0.44    inference(resolution,[],[f61,f44])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl3_10),
% 0.22/0.44    inference(avatar_split_clause,[],[f30,f72])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    spl3_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f29,f68])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl3_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f28,f64])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f27,f60])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f56])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f25,f52])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f47])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(nnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f22,f42])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    spl3_1 | spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f36,f32])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ~spl3_1 | ~spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f36,f32])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (18726)------------------------------
% 0.22/0.44  % (18726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (18726)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (18726)Memory used [KB]: 10746
% 0.22/0.44  % (18726)Time elapsed: 0.015 s
% 0.22/0.44  % (18726)------------------------------
% 0.22/0.44  % (18726)------------------------------
% 0.22/0.45  % (18720)Success in time 0.084 s
%------------------------------------------------------------------------------
