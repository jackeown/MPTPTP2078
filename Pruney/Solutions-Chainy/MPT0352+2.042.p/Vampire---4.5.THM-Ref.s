%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 253 expanded)
%              Number of leaves         :   32 ( 126 expanded)
%              Depth                    :    8
%              Number of atoms          :  346 ( 732 expanded)
%              Number of equality atoms :   49 ( 108 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f558,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f36,f41,f46,f50,f54,f58,f62,f66,f74,f79,f97,f103,f112,f118,f129,f135,f162,f182,f252,f497,f508,f513,f518,f554,f557])).

fof(f557,plain,
    ( spl3_13
    | ~ spl3_72 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | spl3_13
    | ~ spl3_72 ),
    inference(resolution,[],[f538,f89])).

fof(f89,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_13
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f538,plain,
    ( ! [X2] : r1_tarski(k4_xboole_0(X2,sK2),k4_xboole_0(X2,sK1))
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f537])).

fof(f537,plain,
    ( spl3_72
  <=> ! [X2] : r1_tarski(k4_xboole_0(X2,sK2),k4_xboole_0(X2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f554,plain,
    ( spl3_72
    | ~ spl3_5
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f527,f516,f48,f537])).

fof(f48,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f516,plain,
    ( spl3_70
  <=> ! [X0] : k4_xboole_0(X0,sK1) = k2_xboole_0(k4_xboole_0(X0,sK2),k3_xboole_0(X0,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f527,plain,
    ( ! [X14] : r1_tarski(k4_xboole_0(X14,sK2),k4_xboole_0(X14,sK1))
    | ~ spl3_5
    | ~ spl3_70 ),
    inference(superposition,[],[f49,f517])).

fof(f517,plain,
    ( ! [X0] : k4_xboole_0(X0,sK1) = k2_xboole_0(k4_xboole_0(X0,sK2),k3_xboole_0(X0,k4_xboole_0(sK2,sK1)))
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f516])).

fof(f49,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f518,plain,
    ( spl3_70
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f514,f64,f28,f516])).

fof(f28,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f514,plain,
    ( ! [X0] : k4_xboole_0(X0,sK1) = k2_xboole_0(k4_xboole_0(X0,sK2),k3_xboole_0(X0,k4_xboole_0(sK2,sK1)))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f29,f65])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,X1)
        | k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f29,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f513,plain,
    ( ~ spl3_13
    | spl3_2
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f510,f76,f71,f32,f88])).

fof(f32,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f71,plain,
    ( spl3_10
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f76,plain,
    ( spl3_11
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f510,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_2
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f509,f73])).

fof(f73,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f509,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl3_2
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f34,f78])).

fof(f78,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f34,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f508,plain,
    ( spl3_1
    | ~ spl3_23
    | ~ spl3_25
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f501,f495,f178,f158,f28])).

fof(f158,plain,
    ( spl3_23
  <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f178,plain,
    ( spl3_25
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f495,plain,
    ( spl3_69
  <=> ! [X11] : r1_tarski(k4_xboole_0(X11,k4_xboole_0(sK0,sK1)),k4_xboole_0(X11,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f501,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_23
    | ~ spl3_25
    | ~ spl3_69 ),
    inference(forward_demodulation,[],[f499,f160])).

fof(f160,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f158])).

fof(f499,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl3_25
    | ~ spl3_69 ),
    inference(superposition,[],[f496,f180])).

fof(f180,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f178])).

fof(f496,plain,
    ( ! [X11] : r1_tarski(k4_xboole_0(X11,k4_xboole_0(sK0,sK1)),k4_xboole_0(X11,k4_xboole_0(sK0,sK2)))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f495])).

fof(f497,plain,
    ( spl3_69
    | ~ spl3_5
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f471,f250,f48,f495])).

fof(f250,plain,
    ( spl3_30
  <=> ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k3_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f471,plain,
    ( ! [X11] : r1_tarski(k4_xboole_0(X11,k4_xboole_0(sK0,sK1)),k4_xboole_0(X11,k4_xboole_0(sK0,sK2)))
    | ~ spl3_5
    | ~ spl3_30 ),
    inference(superposition,[],[f49,f251])).

fof(f251,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k3_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f250])).

fof(f252,plain,
    ( spl3_30
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f248,f76,f71,f64,f32,f250])).

fof(f248,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k3_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))))
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f247,f78])).

fof(f247,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(X3,k3_subset_1(sK0,sK1)),k3_xboole_0(X3,k4_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK2))))
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f241,f73])).

fof(f241,plain,
    ( ! [X3] : k4_xboole_0(X3,k3_subset_1(sK0,sK2)) = k2_xboole_0(k4_xboole_0(X3,k3_subset_1(sK0,sK1)),k3_xboole_0(X3,k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))))
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f65,f33])).

fof(f33,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f182,plain,
    ( spl3_25
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f175,f132,f115,f178])).

fof(f115,plain,
    ( spl3_17
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f132,plain,
    ( spl3_19
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f175,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(superposition,[],[f134,f117])).

fof(f117,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f115])).

fof(f134,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f132])).

fof(f162,plain,
    ( spl3_23
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f155,f126,f100,f158])).

fof(f100,plain,
    ( spl3_15
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f126,plain,
    ( spl3_18
  <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f155,plain,
    ( sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(superposition,[],[f128,f102])).

fof(f102,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f128,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f126])).

fof(f135,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f130,f76,f60,f43,f132])).

fof(f43,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f60,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f130,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f120,f78])).

fof(f120,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f129,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f124,f71,f60,f38,f126])).

fof(f38,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f124,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f119,f73])).

fof(f119,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f118,plain,
    ( spl3_17
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f113,f109,f56,f115])).

fof(f56,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f109,plain,
    ( spl3_16
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f113,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(resolution,[],[f111,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f111,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f112,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f107,f76,f52,f43,f109])).

fof(f52,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f107,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f105,f45])).

fof(f105,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f53,f78])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f103,plain,
    ( spl3_15
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f98,f94,f56,f100])).

fof(f94,plain,
    ( spl3_14
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f98,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(resolution,[],[f96,f57])).

fof(f96,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f97,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f92,f71,f52,f38,f94])).

fof(f92,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f85,f40])).

fof(f85,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f53,f73])).

fof(f79,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f68,f56,f43,f76])).

fof(f68,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f57,f45])).

fof(f74,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f67,f56,f38,f71])).

fof(f67,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f57,f40])).

fof(f66,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f62,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f58,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f54,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f50,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

% (26661)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
fof(f46,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

% (26660)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
fof(f17,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | ~ r1_tarski(sK1,sK2) )
    & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
      | r1_tarski(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | ~ r1_tarski(sK1,X2) )
          & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
            | r1_tarski(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | ~ r1_tarski(sK1,X2) )
        & ( r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1))
          | r1_tarski(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | ~ r1_tarski(sK1,sK2) )
      & ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
        | r1_tarski(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f41,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f20,f32,f28])).

% (26664)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f20,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f21,f32,f28])).

fof(f21,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:45:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (26665)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (26665)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f558,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f35,f36,f41,f46,f50,f54,f58,f62,f66,f74,f79,f97,f103,f112,f118,f129,f135,f162,f182,f252,f497,f508,f513,f518,f554,f557])).
% 0.21/0.42  fof(f557,plain,(
% 0.21/0.42    spl3_13 | ~spl3_72),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f555])).
% 0.21/0.42  fof(f555,plain,(
% 0.21/0.42    $false | (spl3_13 | ~spl3_72)),
% 0.21/0.42    inference(resolution,[],[f538,f89])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl3_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f88])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    spl3_13 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.42  fof(f538,plain,(
% 0.21/0.42    ( ! [X2] : (r1_tarski(k4_xboole_0(X2,sK2),k4_xboole_0(X2,sK1))) ) | ~spl3_72),
% 0.21/0.42    inference(avatar_component_clause,[],[f537])).
% 0.21/0.42  fof(f537,plain,(
% 0.21/0.42    spl3_72 <=> ! [X2] : r1_tarski(k4_xboole_0(X2,sK2),k4_xboole_0(X2,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.21/0.42  fof(f554,plain,(
% 0.21/0.42    spl3_72 | ~spl3_5 | ~spl3_70),
% 0.21/0.42    inference(avatar_split_clause,[],[f527,f516,f48,f537])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl3_5 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.42  fof(f516,plain,(
% 0.21/0.42    spl3_70 <=> ! [X0] : k4_xboole_0(X0,sK1) = k2_xboole_0(k4_xboole_0(X0,sK2),k3_xboole_0(X0,k4_xboole_0(sK2,sK1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 0.21/0.42  fof(f527,plain,(
% 0.21/0.42    ( ! [X14] : (r1_tarski(k4_xboole_0(X14,sK2),k4_xboole_0(X14,sK1))) ) | (~spl3_5 | ~spl3_70)),
% 0.21/0.42    inference(superposition,[],[f49,f517])).
% 0.21/0.42  fof(f517,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,sK1) = k2_xboole_0(k4_xboole_0(X0,sK2),k3_xboole_0(X0,k4_xboole_0(sK2,sK1)))) ) | ~spl3_70),
% 0.21/0.42    inference(avatar_component_clause,[],[f516])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f48])).
% 0.21/0.42  fof(f518,plain,(
% 0.21/0.42    spl3_70 | ~spl3_1 | ~spl3_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f514,f64,f28,f516])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    spl3_9 <=> ! [X1,X0,X2] : (k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) | ~r1_tarski(X2,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.42  fof(f514,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,sK1) = k2_xboole_0(k4_xboole_0(X0,sK2),k3_xboole_0(X0,k4_xboole_0(sK2,sK1)))) ) | (~spl3_1 | ~spl3_9)),
% 0.21/0.42    inference(resolution,[],[f29,f65])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))) ) | ~spl3_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f64])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f28])).
% 0.21/0.42  fof(f513,plain,(
% 0.21/0.42    ~spl3_13 | spl3_2 | ~spl3_10 | ~spl3_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f510,f76,f71,f32,f88])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl3_2 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    spl3_10 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl3_11 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.42  fof(f510,plain,(
% 0.21/0.42    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | (spl3_2 | ~spl3_10 | ~spl3_11)),
% 0.21/0.42    inference(forward_demodulation,[],[f509,f73])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl3_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f71])).
% 0.21/0.42  fof(f509,plain,(
% 0.21/0.42    ~r1_tarski(k3_subset_1(sK0,sK2),k4_xboole_0(sK0,sK1)) | (spl3_2 | ~spl3_11)),
% 0.21/0.42    inference(forward_demodulation,[],[f34,f78])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl3_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f76])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f508,plain,(
% 0.21/0.42    spl3_1 | ~spl3_23 | ~spl3_25 | ~spl3_69),
% 0.21/0.42    inference(avatar_split_clause,[],[f501,f495,f178,f158,f28])).
% 0.21/0.42  fof(f158,plain,(
% 0.21/0.42    spl3_23 <=> sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.42  fof(f178,plain,(
% 0.21/0.42    spl3_25 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.42  fof(f495,plain,(
% 0.21/0.42    spl3_69 <=> ! [X11] : r1_tarski(k4_xboole_0(X11,k4_xboole_0(sK0,sK1)),k4_xboole_0(X11,k4_xboole_0(sK0,sK2)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.21/0.42  fof(f501,plain,(
% 0.21/0.42    r1_tarski(sK1,sK2) | (~spl3_23 | ~spl3_25 | ~spl3_69)),
% 0.21/0.42    inference(forward_demodulation,[],[f499,f160])).
% 0.21/0.42  fof(f160,plain,(
% 0.21/0.42    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_23),
% 0.21/0.42    inference(avatar_component_clause,[],[f158])).
% 0.21/0.42  fof(f499,plain,(
% 0.21/0.42    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (~spl3_25 | ~spl3_69)),
% 0.21/0.42    inference(superposition,[],[f496,f180])).
% 0.21/0.42  fof(f180,plain,(
% 0.21/0.42    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_25),
% 0.21/0.42    inference(avatar_component_clause,[],[f178])).
% 0.21/0.42  fof(f496,plain,(
% 0.21/0.42    ( ! [X11] : (r1_tarski(k4_xboole_0(X11,k4_xboole_0(sK0,sK1)),k4_xboole_0(X11,k4_xboole_0(sK0,sK2)))) ) | ~spl3_69),
% 0.21/0.42    inference(avatar_component_clause,[],[f495])).
% 0.21/0.42  fof(f497,plain,(
% 0.21/0.42    spl3_69 | ~spl3_5 | ~spl3_30),
% 0.21/0.42    inference(avatar_split_clause,[],[f471,f250,f48,f495])).
% 0.21/0.42  fof(f250,plain,(
% 0.21/0.42    spl3_30 <=> ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k3_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.42  fof(f471,plain,(
% 0.21/0.42    ( ! [X11] : (r1_tarski(k4_xboole_0(X11,k4_xboole_0(sK0,sK1)),k4_xboole_0(X11,k4_xboole_0(sK0,sK2)))) ) | (~spl3_5 | ~spl3_30)),
% 0.21/0.42    inference(superposition,[],[f49,f251])).
% 0.21/0.42  fof(f251,plain,(
% 0.21/0.42    ( ! [X3] : (k4_xboole_0(X3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k3_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))))) ) | ~spl3_30),
% 0.21/0.42    inference(avatar_component_clause,[],[f250])).
% 0.21/0.42  fof(f252,plain,(
% 0.21/0.42    spl3_30 | ~spl3_2 | ~spl3_9 | ~spl3_10 | ~spl3_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f248,f76,f71,f64,f32,f250])).
% 0.21/0.42  fof(f248,plain,(
% 0.21/0.42    ( ! [X3] : (k4_xboole_0(X3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(sK0,sK1)),k3_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))))) ) | (~spl3_2 | ~spl3_9 | ~spl3_10 | ~spl3_11)),
% 0.21/0.42    inference(forward_demodulation,[],[f247,f78])).
% 0.21/0.42  fof(f247,plain,(
% 0.21/0.42    ( ! [X3] : (k4_xboole_0(X3,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(X3,k3_subset_1(sK0,sK1)),k3_xboole_0(X3,k4_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(sK0,sK2))))) ) | (~spl3_2 | ~spl3_9 | ~spl3_10)),
% 0.21/0.42    inference(forward_demodulation,[],[f241,f73])).
% 0.21/0.42  fof(f241,plain,(
% 0.21/0.42    ( ! [X3] : (k4_xboole_0(X3,k3_subset_1(sK0,sK2)) = k2_xboole_0(k4_xboole_0(X3,k3_subset_1(sK0,sK1)),k3_xboole_0(X3,k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))))) ) | (~spl3_2 | ~spl3_9)),
% 0.21/0.42    inference(resolution,[],[f65,f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f182,plain,(
% 0.21/0.42    spl3_25 | ~spl3_17 | ~spl3_19),
% 0.21/0.42    inference(avatar_split_clause,[],[f175,f132,f115,f178])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    spl3_17 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    spl3_19 <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.42  fof(f175,plain,(
% 0.21/0.42    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_17 | ~spl3_19)),
% 0.21/0.42    inference(superposition,[],[f134,f117])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f115])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f132])).
% 0.21/0.42  fof(f162,plain,(
% 0.21/0.42    spl3_23 | ~spl3_15 | ~spl3_18),
% 0.21/0.42    inference(avatar_split_clause,[],[f155,f126,f100,f158])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    spl3_15 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    spl3_18 <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.42  fof(f155,plain,(
% 0.21/0.42    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_15 | ~spl3_18)),
% 0.21/0.42    inference(superposition,[],[f128,f102])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f100])).
% 0.21/0.42  fof(f128,plain,(
% 0.21/0.42    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f126])).
% 0.21/0.42  fof(f135,plain,(
% 0.21/0.42    spl3_19 | ~spl3_4 | ~spl3_8 | ~spl3_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f130,f76,f60,f43,f132])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl3_8 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_4 | ~spl3_8 | ~spl3_11)),
% 0.21/0.42    inference(forward_demodulation,[],[f120,f78])).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | (~spl3_4 | ~spl3_8)),
% 0.21/0.42    inference(resolution,[],[f61,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f43])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) ) | ~spl3_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f60])).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    spl3_18 | ~spl3_3 | ~spl3_8 | ~spl3_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f124,f71,f60,f38,f126])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_3 | ~spl3_8 | ~spl3_10)),
% 0.21/0.42    inference(forward_demodulation,[],[f119,f73])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | (~spl3_3 | ~spl3_8)),
% 0.21/0.42    inference(resolution,[],[f61,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    spl3_17 | ~spl3_7 | ~spl3_16),
% 0.21/0.42    inference(avatar_split_clause,[],[f113,f109,f56,f115])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl3_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    spl3_16 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_7 | ~spl3_16)),
% 0.21/0.42    inference(resolution,[],[f111,f57])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl3_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f56])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f109])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    spl3_16 | ~spl3_4 | ~spl3_6 | ~spl3_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f107,f76,f52,f43,f109])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl3_6 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_4 | ~spl3_6 | ~spl3_11)),
% 0.21/0.42    inference(subsumption_resolution,[],[f105,f45])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_6 | ~spl3_11)),
% 0.21/0.42    inference(superposition,[],[f53,f78])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f52])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl3_15 | ~spl3_7 | ~spl3_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f98,f94,f56,f100])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    spl3_14 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_7 | ~spl3_14)),
% 0.21/0.42    inference(resolution,[],[f96,f57])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f94])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    spl3_14 | ~spl3_3 | ~spl3_6 | ~spl3_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f92,f71,f52,f38,f94])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_3 | ~spl3_6 | ~spl3_10)),
% 0.21/0.42    inference(subsumption_resolution,[],[f85,f40])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | (~spl3_6 | ~spl3_10)),
% 0.21/0.43    inference(superposition,[],[f53,f73])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    spl3_11 | ~spl3_4 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f68,f56,f43,f76])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_7)),
% 0.21/0.43    inference(resolution,[],[f57,f45])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    spl3_10 | ~spl3_3 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f67,f56,f38,f71])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | (~spl3_3 | ~spl3_7)),
% 0.21/0.43    inference(resolution,[],[f57,f40])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    spl3_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f64])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) | ~r1_tarski(X2,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) | ~r1_tarski(X2,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f60])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f56])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f52])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f48])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.43  % (26661)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f43])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  % (26660)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X2] : ((~r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,X2)) & (r1_tarski(k3_subset_1(sK0,X2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)) & (r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(flattening,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f19,f38])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    spl3_1 | spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f32,f28])).
% 0.21/0.43  % (26664)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ~spl3_1 | ~spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f32,f28])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (26665)------------------------------
% 0.21/0.43  % (26665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (26665)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (26665)Memory used [KB]: 10874
% 0.21/0.43  % (26665)Time elapsed: 0.015 s
% 0.21/0.43  % (26665)------------------------------
% 0.21/0.43  % (26665)------------------------------
% 0.21/0.43  % (26659)Success in time 0.072 s
%------------------------------------------------------------------------------
