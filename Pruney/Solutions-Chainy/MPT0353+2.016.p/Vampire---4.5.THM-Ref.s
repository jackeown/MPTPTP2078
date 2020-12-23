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
% DateTime   : Thu Dec  3 12:44:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 175 expanded)
%              Number of leaves         :   27 (  80 expanded)
%              Depth                    :    8
%              Number of atoms          :  261 ( 458 expanded)
%              Number of equality atoms :   65 ( 114 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f61,f65,f72,f76,f80,f90,f95,f99,f165,f255,f277,f340,f380])).

fof(f380,plain,
    ( spl3_26
    | ~ spl3_30
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | spl3_26
    | ~ spl3_30
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f254,f378])).

fof(f378,plain,
    ( ! [X2] : k3_xboole_0(sK1,k4_xboole_0(sK0,X2)) = k4_xboole_0(sK1,X2)
    | ~ spl3_30
    | ~ spl3_33 ),
    inference(superposition,[],[f339,f276])).

fof(f276,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl3_30
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f339,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl3_33
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f254,plain,
    ( k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | spl3_26 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl3_26
  <=> k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f340,plain,
    ( spl3_33
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f114,f78,f51,f338])).

fof(f51,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f78,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f114,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f79,f52])).

fof(f52,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f79,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f277,plain,
    ( spl3_30
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f156,f92,f74,f70,f59,f36,f274])).

fof(f36,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f59,plain,
    ( spl3_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f70,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f74,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f92,plain,
    ( spl3_13
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f156,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f155,f113])).

fof(f113,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f105,f100])).

fof(f100,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f38,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f38,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f105,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f38,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f155,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f154,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f154,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f149,f100])).

fof(f149,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f94,f71])).

fof(f94,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f255,plain,
    ( ~ spl3_26
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f167,f162,f97,f88,f70,f46,f41,f36,f252])).

fof(f41,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( spl3_3
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f88,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f97,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f162,plain,
    ( spl3_15
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f167,plain,
    ( k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f145,f166])).

fof(f166,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f164,f101])).

fof(f101,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f43,f71])).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f164,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f162])).

fof(f145,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f144,f101])).

% (4165)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f144,plain,
    ( k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f143,f138])).

fof(f138,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0)
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f38,f89])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f143,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f142,f101])).

fof(f142,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl3_3
    | ~ spl3_14 ),
    inference(superposition,[],[f48,f98])).

fof(f98,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f48,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f165,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f86,f63,f41,f162])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f86,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f43,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f99,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f34,f97])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f95,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f85,f63,f36,f92])).

fof(f85,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f38,f64])).

fof(f90,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f33,f88])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f80,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f76,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f72,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f61,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f49,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (4161)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.43  % (4163)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (4164)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (4162)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (4156)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (4169)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (4159)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (4160)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (4153)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (4168)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (4167)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (4151)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (4154)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (4155)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (4166)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (4157)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (4158)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (4157)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f381,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f61,f65,f72,f76,f80,f90,f95,f99,f165,f255,f277,f340,f380])).
% 0.21/0.52  fof(f380,plain,(
% 0.21/0.52    spl3_26 | ~spl3_30 | ~spl3_33),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f379])).
% 0.21/0.52  fof(f379,plain,(
% 0.21/0.52    $false | (spl3_26 | ~spl3_30 | ~spl3_33)),
% 0.21/0.52    inference(subsumption_resolution,[],[f254,f378])).
% 0.21/0.52  fof(f378,plain,(
% 0.21/0.52    ( ! [X2] : (k3_xboole_0(sK1,k4_xboole_0(sK0,X2)) = k4_xboole_0(sK1,X2)) ) | (~spl3_30 | ~spl3_33)),
% 0.21/0.52    inference(superposition,[],[f339,f276])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f274])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    spl3_30 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.52  fof(f339,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)) ) | ~spl3_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f338])).
% 0.21/0.52  fof(f338,plain,(
% 0.21/0.52    spl3_33 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | spl3_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f252])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    spl3_26 <=> k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    spl3_33 | ~spl3_4 | ~spl3_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f114,f78,f51,f338])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl3_10 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)) ) | (~spl3_4 | ~spl3_10)),
% 0.21/0.52    inference(superposition,[],[f79,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    spl3_30 | ~spl3_1 | ~spl3_6 | ~spl3_8 | ~spl3_9 | ~spl3_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f156,f92,f74,f70,f59,f36,f274])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl3_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl3_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl3_9 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl3_13 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    sK1 = k3_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_6 | ~spl3_8 | ~spl3_9 | ~spl3_13)),
% 0.21/0.52    inference(forward_demodulation,[],[f155,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_8 | ~spl3_9)),
% 0.21/0.52    inference(forward_demodulation,[],[f105,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f38,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f36])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | (~spl3_1 | ~spl3_9)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f38,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f74])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_6 | ~spl3_8 | ~spl3_13)),
% 0.21/0.52    inference(forward_demodulation,[],[f154,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f59])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_8 | ~spl3_13)),
% 0.21/0.52    inference(forward_demodulation,[],[f149,f100])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) | (~spl3_8 | ~spl3_13)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f94,f71])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f255,plain,(
% 0.21/0.52    ~spl3_26 | ~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_12 | ~spl3_14 | ~spl3_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f167,f162,f97,f88,f70,f46,f41,f36,f252])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    spl3_3 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl3_12 <=> ! [X1,X0,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl3_14 <=> ! [X1,X0,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl3_15 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_12 | ~spl3_14 | ~spl3_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f145,f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_8 | ~spl3_15)),
% 0.21/0.52    inference(forward_demodulation,[],[f164,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f43,f71])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f41])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f162])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_12 | ~spl3_14)),
% 0.21/0.52    inference(forward_demodulation,[],[f144,f101])).
% 0.21/0.52  % (4165)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_12 | ~spl3_14)),
% 0.21/0.53    inference(forward_demodulation,[],[f143,f138])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0)) ) | (~spl3_1 | ~spl3_12)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f38,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f88])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_14)),
% 0.21/0.53    inference(forward_demodulation,[],[f142,f101])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | (spl3_3 | ~spl3_14)),
% 0.21/0.53    inference(superposition,[],[f48,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f46])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    spl3_15 | ~spl3_2 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f86,f63,f41,f162])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl3_7 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_7)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f43,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl3_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f97])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    spl3_13 | ~spl3_1 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f85,f63,f36,f92])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_7)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f38,f64])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl3_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f88])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f31,f78])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    spl3_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f30,f74])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl3_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f29,f70])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f28,f63])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f27,f59])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f25,f51])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f24,f46])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f23,f41])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f22,f36])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (4157)------------------------------
% 0.21/0.53  % (4157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4157)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (4157)Memory used [KB]: 6396
% 0.21/0.53  % (4157)Time elapsed: 0.113 s
% 0.21/0.53  % (4157)------------------------------
% 0.21/0.53  % (4157)------------------------------
% 0.21/0.54  % (4150)Success in time 0.18 s
%------------------------------------------------------------------------------
