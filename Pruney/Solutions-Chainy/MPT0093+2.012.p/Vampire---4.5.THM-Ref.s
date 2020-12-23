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
% DateTime   : Thu Dec  3 12:31:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 191 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :    7
%              Number of atoms          :  268 ( 465 expanded)
%              Number of equality atoms :   71 ( 127 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2807,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f45,f49,f53,f61,f65,f69,f73,f78,f102,f112,f120,f149,f155,f178,f182,f221,f226,f253,f263,f2744,f2800])).

fof(f2800,plain,
    ( spl3_26
    | ~ spl3_31
    | ~ spl3_233 ),
    inference(avatar_contradiction_clause,[],[f2799])).

fof(f2799,plain,
    ( $false
    | spl3_26
    | ~ spl3_31
    | ~ spl3_233 ),
    inference(subsumption_resolution,[],[f2762,f177])).

fof(f177,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_26
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f2762,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_31
    | ~ spl3_233 ),
    inference(superposition,[],[f220,f2743])).

fof(f2743,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,k4_xboole_0(sK1,X2)))
    | ~ spl3_233 ),
    inference(avatar_component_clause,[],[f2742])).

fof(f2742,plain,
    ( spl3_233
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,k4_xboole_0(sK1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_233])])).

fof(f220,plain,
    ( ! [X14] : k4_xboole_0(sK0,k2_xboole_0(sK2,X14)) = k4_xboole_0(sK0,X14)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl3_31
  <=> ! [X14] : k4_xboole_0(sK0,k2_xboole_0(sK2,X14)) = k4_xboole_0(sK0,X14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f2744,plain,
    ( spl3_233
    | ~ spl3_35
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f2737,f261,f236,f2742])).

fof(f236,plain,
    ( spl3_35
  <=> ! [X7,X8] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f261,plain,
    ( spl3_39
  <=> ! [X0] :
        ( k1_xboole_0 = k4_xboole_0(sK0,X0)
        | k1_xboole_0 != k4_xboole_0(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f2737,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,k4_xboole_0(sK1,X2)))
    | ~ spl3_35
    | ~ spl3_39 ),
    inference(trivial_inequality_removal,[],[f2724])).

% (14269)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
fof(f2724,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,k4_xboole_0(sK1,X2))) )
    | ~ spl3_35
    | ~ spl3_39 ),
    inference(superposition,[],[f262,f237])).

fof(f237,plain,
    ( ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8)))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f236])).

fof(f262,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k4_xboole_0(sK1,X0)
        | k1_xboole_0 = k4_xboole_0(sK0,X0) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f261])).

fof(f263,plain,
    ( spl3_39
    | ~ spl3_27
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f255,f224,f180,f261])).

fof(f180,plain,
    ( spl3_27
  <=> ! [X3,X2] :
        ( k1_xboole_0 != k4_xboole_0(X2,X3)
        | k2_xboole_0(X2,X3) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f224,plain,
    ( spl3_32
  <=> ! [X15] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f255,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k4_xboole_0(sK0,X0)
        | k1_xboole_0 != k4_xboole_0(sK1,X0) )
    | ~ spl3_27
    | ~ spl3_32 ),
    inference(superposition,[],[f225,f181])).

fof(f181,plain,
    ( ! [X2,X3] :
        ( k2_xboole_0(X2,X3) = X3
        | k1_xboole_0 != k4_xboole_0(X2,X3) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f180])).

fof(f225,plain,
    ( ! [X15] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X15))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f224])).

fof(f253,plain,
    ( spl3_35
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f199,f118,f71,f236])).

fof(f71,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f118,plain,
    ( spl3_19
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

% (14276)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
fof(f199,plain,
    ( ! [X14,X13] : k1_xboole_0 = k4_xboole_0(X13,k2_xboole_0(X14,k4_xboole_0(X13,X14)))
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(superposition,[],[f119,f72])).

fof(f72,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f119,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f118])).

fof(f226,plain,
    ( spl3_32
    | ~ spl3_11
    | ~ spl3_17
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f222,f153,f109,f71,f224])).

fof(f109,plain,
    ( spl3_17
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f153,plain,
    ( spl3_25
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f222,plain,
    ( ! [X15] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X15))
    | ~ spl3_11
    | ~ spl3_17
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f190,f154])).

fof(f154,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f153])).

fof(f190,plain,
    ( ! [X15] : k4_xboole_0(sK0,k2_xboole_0(sK1,X15)) = k4_xboole_0(k1_xboole_0,X15)
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(superposition,[],[f72,f111])).

fof(f111,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f109])).

fof(f221,plain,
    ( spl3_31
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f189,f99,f71,f219])).

fof(f99,plain,
    ( spl3_16
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f189,plain,
    ( ! [X14] : k4_xboole_0(sK0,k2_xboole_0(sK2,X14)) = k4_xboole_0(sK0,X14)
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(superposition,[],[f72,f101])).

fof(f101,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f182,plain,
    ( spl3_27
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f173,f67,f51,f180])).

fof(f51,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f67,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f173,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != k4_xboole_0(X2,X3)
        | k2_xboole_0(X2,X3) = X3 )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f178,plain,
    ( ~ spl3_26
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f171,f67,f28,f175])).

fof(f28,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f171,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f68,f30])).

fof(f30,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f155,plain,
    ( spl3_25
    | ~ spl3_9
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f150,f147,f63,f153])).

fof(f63,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f147,plain,
    ( spl3_24
  <=> ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f150,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_9
    | ~ spl3_24 ),
    inference(resolution,[],[f148,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f148,plain,
    ( ! [X1] : r1_tarski(k1_xboole_0,X1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( spl3_24
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f141,f118,f47,f147])).

fof(f47,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f141,plain,
    ( ! [X1] : r1_tarski(k1_xboole_0,X1)
    | ~ spl3_5
    | ~ spl3_19 ),
    inference(superposition,[],[f48,f119])).

fof(f48,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f120,plain,
    ( spl3_19
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f107,f76,f63,f118])).

fof(f76,plain,
    ( spl3_12
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f107,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(resolution,[],[f64,f77])).

fof(f77,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f76])).

fof(f112,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f105,f63,f38,f109])).

fof(f38,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f105,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f64,f40])).

fof(f40,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f102,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f96,f59,f33,f99])).

fof(f33,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f96,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f60,f35])).

fof(f35,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f78,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f74,f47,f43,f76])).

fof(f43,plain,
    ( spl3_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f74,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f48,f44])).

fof(f44,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f73,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f26,f71])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f69,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f65,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f59])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f53,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f49,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f45,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f41,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f28])).

fof(f18,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (14271)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (14273)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (14272)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.44  % (14266)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.44  % (14275)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.44  % (14270)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.45  % (14267)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.45  % (14274)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.46  % (14271)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f2807,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f31,f36,f41,f45,f49,f53,f61,f65,f69,f73,f78,f102,f112,f120,f149,f155,f178,f182,f221,f226,f253,f263,f2744,f2800])).
% 0.20/0.46  fof(f2800,plain,(
% 0.20/0.46    spl3_26 | ~spl3_31 | ~spl3_233),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f2799])).
% 0.20/0.46  fof(f2799,plain,(
% 0.20/0.46    $false | (spl3_26 | ~spl3_31 | ~spl3_233)),
% 0.20/0.46    inference(subsumption_resolution,[],[f2762,f177])).
% 0.20/0.46  fof(f177,plain,(
% 0.20/0.46    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_26),
% 0.20/0.46    inference(avatar_component_clause,[],[f175])).
% 0.20/0.46  fof(f175,plain,(
% 0.20/0.46    spl3_26 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.46  fof(f2762,plain,(
% 0.20/0.46    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_31 | ~spl3_233)),
% 0.20/0.46    inference(superposition,[],[f220,f2743])).
% 0.20/0.46  fof(f2743,plain,(
% 0.20/0.46    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,k4_xboole_0(sK1,X2)))) ) | ~spl3_233),
% 0.20/0.46    inference(avatar_component_clause,[],[f2742])).
% 0.20/0.46  fof(f2742,plain,(
% 0.20/0.46    spl3_233 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,k4_xboole_0(sK1,X2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_233])])).
% 0.20/0.46  fof(f220,plain,(
% 0.20/0.46    ( ! [X14] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X14)) = k4_xboole_0(sK0,X14)) ) | ~spl3_31),
% 0.20/0.46    inference(avatar_component_clause,[],[f219])).
% 0.20/0.46  fof(f219,plain,(
% 0.20/0.46    spl3_31 <=> ! [X14] : k4_xboole_0(sK0,k2_xboole_0(sK2,X14)) = k4_xboole_0(sK0,X14)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.46  fof(f2744,plain,(
% 0.20/0.46    spl3_233 | ~spl3_35 | ~spl3_39),
% 0.20/0.46    inference(avatar_split_clause,[],[f2737,f261,f236,f2742])).
% 0.20/0.46  fof(f236,plain,(
% 0.20/0.46    spl3_35 <=> ! [X7,X8] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.46  fof(f261,plain,(
% 0.20/0.46    spl3_39 <=> ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,X0) | k1_xboole_0 != k4_xboole_0(sK1,X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.46  fof(f2737,plain,(
% 0.20/0.46    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,k4_xboole_0(sK1,X2)))) ) | (~spl3_35 | ~spl3_39)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f2724])).
% 0.20/0.46  % (14269)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.46  fof(f2724,plain,(
% 0.20/0.46    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,k4_xboole_0(sK1,X2)))) ) | (~spl3_35 | ~spl3_39)),
% 0.20/0.46    inference(superposition,[],[f262,f237])).
% 0.20/0.46  fof(f237,plain,(
% 0.20/0.46    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8)))) ) | ~spl3_35),
% 0.20/0.46    inference(avatar_component_clause,[],[f236])).
% 0.20/0.46  fof(f262,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(sK1,X0) | k1_xboole_0 = k4_xboole_0(sK0,X0)) ) | ~spl3_39),
% 0.20/0.46    inference(avatar_component_clause,[],[f261])).
% 0.20/0.46  fof(f263,plain,(
% 0.20/0.46    spl3_39 | ~spl3_27 | ~spl3_32),
% 0.20/0.46    inference(avatar_split_clause,[],[f255,f224,f180,f261])).
% 0.20/0.46  fof(f180,plain,(
% 0.20/0.46    spl3_27 <=> ! [X3,X2] : (k1_xboole_0 != k4_xboole_0(X2,X3) | k2_xboole_0(X2,X3) = X3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.46  fof(f224,plain,(
% 0.20/0.46    spl3_32 <=> ! [X15] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X15))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.46  fof(f255,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,X0) | k1_xboole_0 != k4_xboole_0(sK1,X0)) ) | (~spl3_27 | ~spl3_32)),
% 0.20/0.46    inference(superposition,[],[f225,f181])).
% 0.20/0.46  fof(f181,plain,(
% 0.20/0.46    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X3 | k1_xboole_0 != k4_xboole_0(X2,X3)) ) | ~spl3_27),
% 0.20/0.46    inference(avatar_component_clause,[],[f180])).
% 0.20/0.46  fof(f225,plain,(
% 0.20/0.46    ( ! [X15] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X15))) ) | ~spl3_32),
% 0.20/0.46    inference(avatar_component_clause,[],[f224])).
% 0.20/0.46  fof(f253,plain,(
% 0.20/0.46    spl3_35 | ~spl3_11 | ~spl3_19),
% 0.20/0.46    inference(avatar_split_clause,[],[f199,f118,f71,f236])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    spl3_11 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    spl3_19 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.46  % (14276)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.46  fof(f199,plain,(
% 0.20/0.46    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(X13,k2_xboole_0(X14,k4_xboole_0(X13,X14)))) ) | (~spl3_11 | ~spl3_19)),
% 0.20/0.46    inference(superposition,[],[f119,f72])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f71])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl3_19),
% 0.20/0.46    inference(avatar_component_clause,[],[f118])).
% 0.20/0.46  fof(f226,plain,(
% 0.20/0.46    spl3_32 | ~spl3_11 | ~spl3_17 | ~spl3_25),
% 0.20/0.46    inference(avatar_split_clause,[],[f222,f153,f109,f71,f224])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    spl3_17 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.46  fof(f153,plain,(
% 0.20/0.46    spl3_25 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.46  fof(f222,plain,(
% 0.20/0.46    ( ! [X15] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X15))) ) | (~spl3_11 | ~spl3_17 | ~spl3_25)),
% 0.20/0.46    inference(forward_demodulation,[],[f190,f154])).
% 0.20/0.46  fof(f154,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl3_25),
% 0.20/0.46    inference(avatar_component_clause,[],[f153])).
% 0.20/0.46  fof(f190,plain,(
% 0.20/0.46    ( ! [X15] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X15)) = k4_xboole_0(k1_xboole_0,X15)) ) | (~spl3_11 | ~spl3_17)),
% 0.20/0.46    inference(superposition,[],[f72,f111])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_17),
% 0.20/0.46    inference(avatar_component_clause,[],[f109])).
% 0.20/0.46  fof(f221,plain,(
% 0.20/0.46    spl3_31 | ~spl3_11 | ~spl3_16),
% 0.20/0.46    inference(avatar_split_clause,[],[f189,f99,f71,f219])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    spl3_16 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.46  fof(f189,plain,(
% 0.20/0.46    ( ! [X14] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X14)) = k4_xboole_0(sK0,X14)) ) | (~spl3_11 | ~spl3_16)),
% 0.20/0.46    inference(superposition,[],[f72,f101])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f99])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    spl3_27 | ~spl3_6 | ~spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f173,f67,f51,f180])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl3_6 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl3_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,X3) | k2_xboole_0(X2,X3) = X3) ) | (~spl3_6 | ~spl3_10)),
% 0.20/0.47    inference(resolution,[],[f68,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f51])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) ) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ~spl3_26 | spl3_1 | ~spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f171,f67,f28,f175])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (spl3_1 | ~spl3_10)),
% 0.20/0.47    inference(resolution,[],[f68,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f28])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    spl3_25 | ~spl3_9 | ~spl3_24),
% 0.20/0.47    inference(avatar_split_clause,[],[f150,f147,f63,f153])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl3_9 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    spl3_24 <=> ! [X1] : r1_tarski(k1_xboole_0,X1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl3_9 | ~spl3_24)),
% 0.20/0.47    inference(resolution,[],[f148,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f63])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) ) | ~spl3_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f147])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    spl3_24 | ~spl3_5 | ~spl3_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f141,f118,f47,f147])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    spl3_5 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) ) | (~spl3_5 | ~spl3_19)),
% 0.20/0.47    inference(superposition,[],[f48,f119])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f47])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    spl3_19 | ~spl3_9 | ~spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f107,f76,f63,f118])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl3_12 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | (~spl3_9 | ~spl3_12)),
% 0.20/0.47    inference(resolution,[],[f64,f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    spl3_17 | ~spl3_3 | ~spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f105,f63,f38,f109])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_9)),
% 0.20/0.47    inference(resolution,[],[f64,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f38])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl3_16 | ~spl3_2 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f96,f59,f33,f99])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl3_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_8)),
% 0.20/0.47    inference(resolution,[],[f60,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f33])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl3_12 | ~spl3_4 | ~spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f74,f47,f43,f76])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl3_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl3_4 | ~spl3_5)),
% 0.20/0.47    inference(superposition,[],[f48,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f43])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f71])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f24,f67])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f63])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f59])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f51])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f47])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f43])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f16,f38])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => (~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f33])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f28])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (14271)------------------------------
% 0.20/0.47  % (14271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (14271)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (14271)Memory used [KB]: 12281
% 0.20/0.47  % (14271)Time elapsed: 0.055 s
% 0.20/0.47  % (14271)------------------------------
% 0.20/0.47  % (14271)------------------------------
% 0.20/0.47  % (14265)Success in time 0.114 s
%------------------------------------------------------------------------------
