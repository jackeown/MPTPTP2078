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
% DateTime   : Thu Dec  3 12:37:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 171 expanded)
%              Number of leaves         :   36 (  80 expanded)
%              Depth                    :    7
%              Number of atoms          :  272 ( 379 expanded)
%              Number of equality atoms :   98 ( 144 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f968,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f63,f71,f75,f79,f87,f91,f95,f103,f107,f111,f132,f148,f198,f239,f251,f341,f392,f452,f463,f947,f967])).

fof(f967,plain,
    ( ~ spl2_3
    | ~ spl2_5
    | spl2_17
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_41
    | ~ spl2_43
    | ~ spl2_56 ),
    inference(avatar_contradiction_clause,[],[f966])).

fof(f966,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_5
    | spl2_17
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_41
    | ~ spl2_43
    | ~ spl2_56 ),
    inference(subsumption_resolution,[],[f578,f965])).

fof(f965,plain,
    ( ! [X9] : k2_xboole_0(X9,X9) = X9
    | ~ spl2_3
    | ~ spl2_27
    | ~ spl2_32
    | ~ spl2_41
    | ~ spl2_56 ),
    inference(forward_demodulation,[],[f964,f247])).

fof(f247,plain,
    ( ! [X9] : k4_xboole_0(X9,k1_xboole_0) = X9
    | ~ spl2_3
    | ~ spl2_27
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f245,f62])).

fof(f62,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_3
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f245,plain,
    ( ! [X9] : k4_xboole_0(X9,k1_xboole_0) = k5_xboole_0(X9,k1_xboole_0)
    | ~ spl2_27
    | ~ spl2_32 ),
    inference(superposition,[],[f238,f197])).

fof(f197,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl2_27
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f238,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl2_32
  <=> ! [X3,X4] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f964,plain,
    ( ! [X9] : k4_xboole_0(X9,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X9,k1_xboole_0),X9)
    | ~ spl2_3
    | ~ spl2_41
    | ~ spl2_56 ),
    inference(forward_demodulation,[],[f959,f62])).

% (30111)Refutation not found, incomplete strategy% (30111)------------------------------
% (30111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30111)Termination reason: Refutation not found, incomplete strategy

% (30111)Memory used [KB]: 10618
% (30111)Time elapsed: 0.091 s
% (30111)------------------------------
% (30111)------------------------------
fof(f959,plain,
    ( ! [X9] : k2_xboole_0(k4_xboole_0(X9,k1_xboole_0),X9) = k5_xboole_0(k4_xboole_0(X9,k1_xboole_0),k1_xboole_0)
    | ~ spl2_41
    | ~ spl2_56 ),
    inference(superposition,[],[f391,f946])).

fof(f946,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f945])).

fof(f945,plain,
    ( spl2_56
  <=> ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f391,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl2_41
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f578,plain,
    ( k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl2_5
    | spl2_17
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f569,f70])).

fof(f70,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_5
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f569,plain,
    ( k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | spl2_17
    | ~ spl2_43 ),
    inference(superposition,[],[f131,f451])).

fof(f451,plain,
    ( sK0 = sK1
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl2_43
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f131,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_17 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl2_17
  <=> k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f947,plain,
    ( spl2_56
    | ~ spl2_6
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f199,f196,f73,f945])).

fof(f73,plain,
    ( spl2_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f199,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_27 ),
    inference(superposition,[],[f197,f74])).

fof(f74,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f463,plain,
    ( ~ spl2_18
    | spl2_39
    | spl2_43 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | ~ spl2_18
    | spl2_39
    | spl2_43 ),
    inference(subsumption_resolution,[],[f422,f450])).

fof(f450,plain,
    ( sK0 != sK1
    | spl2_43 ),
    inference(avatar_component_clause,[],[f449])).

fof(f422,plain,
    ( sK0 = sK1
    | ~ spl2_18
    | spl2_39 ),
    inference(trivial_inequality_removal,[],[f421])).

fof(f421,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ spl2_18
    | spl2_39 ),
    inference(superposition,[],[f340,f147])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f340,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_39 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl2_39
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f452,plain,
    ( spl2_43
    | ~ spl2_9
    | spl2_38 ),
    inference(avatar_split_clause,[],[f413,f334,f85,f449])).

fof(f85,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f334,plain,
    ( spl2_38
  <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f413,plain,
    ( sK0 = sK1
    | ~ spl2_9
    | spl2_38 ),
    inference(unit_resulting_resolution,[],[f336,f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f336,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl2_38 ),
    inference(avatar_component_clause,[],[f334])).

fof(f392,plain,
    ( spl2_41
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f142,f109,f101,f390])).

fof(f101,plain,
    ( spl2_13
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f109,plain,
    ( spl2_15
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f142,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(superposition,[],[f102,f110])).

fof(f110,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f102,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f101])).

fof(f341,plain,
    ( ~ spl2_38
    | ~ spl2_39
    | spl2_17
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f266,f249,f129,f338,f334])).

fof(f249,plain,
    ( spl2_33
  <=> ! [X1,X0] :
        ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f266,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl2_17
    | ~ spl2_33 ),
    inference(superposition,[],[f131,f250])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f249])).

fof(f251,plain,
    ( spl2_33
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f133,f101,f93,f249])).

fof(f93,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(superposition,[],[f102,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f239,plain,
    ( spl2_32
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f136,f105,f73,f237])).

fof(f105,plain,
    ( spl2_14
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f136,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(superposition,[],[f106,f74])).

fof(f106,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f105])).

fof(f198,plain,
    ( spl2_27
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f118,f89,f57,f196])).

fof(f57,plain,
    ( spl2_2
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f89,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f118,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f58,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f58,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f148,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f42,f146])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f132,plain,
    ( ~ spl2_17
    | spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f113,f77,f52,f129])).

fof(f52,plain,
    ( spl2_1
  <=> k2_tarski(sK0,sK1) = k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f77,plain,
    ( spl2_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f113,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f54,f78])).

fof(f78,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f54,plain,
    ( k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f111,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f40,f109])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f107,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f39,f105])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f103,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f38,f101])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f95,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f44,f93])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f91,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f87,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f41,f85])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f79,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f75,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f71,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f32,f61])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f59,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f55,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f52])).

fof(f30,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27])).

fof(f27,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 19:24:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.47  % (30104)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (30102)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (30108)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (30105)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (30113)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (30110)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (30103)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (30114)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (30105)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (30115)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (30109)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (30112)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (30100)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.52  % (30107)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (30101)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.52  % (30116)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (30106)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (30111)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f968,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f55,f59,f63,f71,f75,f79,f87,f91,f95,f103,f107,f111,f132,f148,f198,f239,f251,f341,f392,f452,f463,f947,f967])).
% 0.22/0.52  fof(f967,plain,(
% 0.22/0.52    ~spl2_3 | ~spl2_5 | spl2_17 | ~spl2_27 | ~spl2_32 | ~spl2_41 | ~spl2_43 | ~spl2_56),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f966])).
% 0.22/0.52  fof(f966,plain,(
% 0.22/0.52    $false | (~spl2_3 | ~spl2_5 | spl2_17 | ~spl2_27 | ~spl2_32 | ~spl2_41 | ~spl2_43 | ~spl2_56)),
% 0.22/0.52    inference(subsumption_resolution,[],[f578,f965])).
% 0.22/0.52  fof(f965,plain,(
% 0.22/0.52    ( ! [X9] : (k2_xboole_0(X9,X9) = X9) ) | (~spl2_3 | ~spl2_27 | ~spl2_32 | ~spl2_41 | ~spl2_56)),
% 0.22/0.52    inference(forward_demodulation,[],[f964,f247])).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    ( ! [X9] : (k4_xboole_0(X9,k1_xboole_0) = X9) ) | (~spl2_3 | ~spl2_27 | ~spl2_32)),
% 0.22/0.52    inference(forward_demodulation,[],[f245,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl2_3 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.52  fof(f245,plain,(
% 0.22/0.52    ( ! [X9] : (k4_xboole_0(X9,k1_xboole_0) = k5_xboole_0(X9,k1_xboole_0)) ) | (~spl2_27 | ~spl2_32)),
% 0.22/0.52    inference(superposition,[],[f238,f197])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl2_27),
% 0.22/0.52    inference(avatar_component_clause,[],[f196])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    spl2_27 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.52  fof(f238,plain,(
% 0.22/0.52    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))) ) | ~spl2_32),
% 0.22/0.52    inference(avatar_component_clause,[],[f237])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    spl2_32 <=> ! [X3,X4] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.52  fof(f964,plain,(
% 0.22/0.52    ( ! [X9] : (k4_xboole_0(X9,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X9,k1_xboole_0),X9)) ) | (~spl2_3 | ~spl2_41 | ~spl2_56)),
% 0.22/0.52    inference(forward_demodulation,[],[f959,f62])).
% 0.22/0.52  % (30111)Refutation not found, incomplete strategy% (30111)------------------------------
% 0.22/0.52  % (30111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30111)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30111)Memory used [KB]: 10618
% 0.22/0.52  % (30111)Time elapsed: 0.091 s
% 0.22/0.52  % (30111)------------------------------
% 0.22/0.52  % (30111)------------------------------
% 0.22/0.52  fof(f959,plain,(
% 0.22/0.52    ( ! [X9] : (k2_xboole_0(k4_xboole_0(X9,k1_xboole_0),X9) = k5_xboole_0(k4_xboole_0(X9,k1_xboole_0),k1_xboole_0)) ) | (~spl2_41 | ~spl2_56)),
% 0.22/0.52    inference(superposition,[],[f391,f946])).
% 0.22/0.52  fof(f946,plain,(
% 0.22/0.52    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) ) | ~spl2_56),
% 0.22/0.52    inference(avatar_component_clause,[],[f945])).
% 0.22/0.52  fof(f945,plain,(
% 0.22/0.52    spl2_56 <=> ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 0.22/0.52  fof(f391,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_41),
% 0.22/0.52    inference(avatar_component_clause,[],[f390])).
% 0.22/0.52  fof(f390,plain,(
% 0.22/0.52    spl2_41 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.22/0.52  fof(f578,plain,(
% 0.22/0.52    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | (~spl2_5 | spl2_17 | ~spl2_43)),
% 0.22/0.52    inference(forward_demodulation,[],[f569,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl2_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl2_5 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.52  fof(f569,plain,(
% 0.22/0.52    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | (spl2_17 | ~spl2_43)),
% 0.22/0.52    inference(superposition,[],[f131,f451])).
% 0.22/0.52  fof(f451,plain,(
% 0.22/0.52    sK0 = sK1 | ~spl2_43),
% 0.22/0.52    inference(avatar_component_clause,[],[f449])).
% 0.22/0.52  fof(f449,plain,(
% 0.22/0.52    spl2_43 <=> sK0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f129])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    spl2_17 <=> k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.52  fof(f947,plain,(
% 0.22/0.52    spl2_56 | ~spl2_6 | ~spl2_27),
% 0.22/0.52    inference(avatar_split_clause,[],[f199,f196,f73,f945])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl2_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) ) | (~spl2_6 | ~spl2_27)),
% 0.22/0.52    inference(superposition,[],[f197,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f463,plain,(
% 0.22/0.52    ~spl2_18 | spl2_39 | spl2_43),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f462])).
% 0.22/0.53  fof(f462,plain,(
% 0.22/0.53    $false | (~spl2_18 | spl2_39 | spl2_43)),
% 0.22/0.53    inference(subsumption_resolution,[],[f422,f450])).
% 0.22/0.53  fof(f450,plain,(
% 0.22/0.53    sK0 != sK1 | spl2_43),
% 0.22/0.53    inference(avatar_component_clause,[],[f449])).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    sK0 = sK1 | (~spl2_18 | spl2_39)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f421])).
% 0.22/0.53  fof(f421,plain,(
% 0.22/0.53    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | sK0 = sK1 | (~spl2_18 | spl2_39)),
% 0.22/0.53    inference(superposition,[],[f340,f147])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) ) | ~spl2_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f146])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    spl2_18 <=> ! [X1,X0] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.53  fof(f340,plain,(
% 0.22/0.53    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl2_39),
% 0.22/0.53    inference(avatar_component_clause,[],[f338])).
% 0.22/0.53  fof(f338,plain,(
% 0.22/0.53    spl2_39 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.22/0.53  fof(f452,plain,(
% 0.22/0.53    spl2_43 | ~spl2_9 | spl2_38),
% 0.22/0.53    inference(avatar_split_clause,[],[f413,f334,f85,f449])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl2_9 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    spl2_38 <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.22/0.53  fof(f413,plain,(
% 0.22/0.53    sK0 = sK1 | (~spl2_9 | spl2_38)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f336,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) ) | ~spl2_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f85])).
% 0.22/0.53  fof(f336,plain,(
% 0.22/0.53    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl2_38),
% 0.22/0.53    inference(avatar_component_clause,[],[f334])).
% 0.22/0.53  fof(f392,plain,(
% 0.22/0.53    spl2_41 | ~spl2_13 | ~spl2_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f142,f109,f101,f390])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl2_13 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl2_15 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | (~spl2_13 | ~spl2_15)),
% 0.22/0.53    inference(superposition,[],[f102,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f109])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f101])).
% 0.22/0.53  fof(f341,plain,(
% 0.22/0.53    ~spl2_38 | ~spl2_39 | spl2_17 | ~spl2_33),
% 0.22/0.53    inference(avatar_split_clause,[],[f266,f249,f129,f338,f334])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    spl2_33 <=> ! [X1,X0] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.22/0.53  fof(f266,plain,(
% 0.22/0.53    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | (spl2_17 | ~spl2_33)),
% 0.22/0.53    inference(superposition,[],[f131,f250])).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) ) | ~spl2_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f249])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    spl2_33 | ~spl2_11 | ~spl2_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f133,f101,f93,f249])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    spl2_11 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) ) | (~spl2_11 | ~spl2_13)),
% 0.22/0.53    inference(superposition,[],[f102,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl2_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f93])).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    spl2_32 | ~spl2_6 | ~spl2_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f136,f105,f73,f237])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl2_14 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))) ) | (~spl2_6 | ~spl2_14)),
% 0.22/0.53    inference(superposition,[],[f106,f74])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f105])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    spl2_27 | ~spl2_2 | ~spl2_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f118,f89,f57,f196])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl2_2 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl2_10 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl2_2 | ~spl2_10)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f58,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl2_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f42,f146])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.53    inference(ennf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ~spl2_17 | spl2_1 | ~spl2_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f113,f77,f52,f129])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    spl2_1 <=> k2_tarski(sK0,sK1) = k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl2_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | (spl2_1 | ~spl2_7)),
% 0.22/0.53    inference(superposition,[],[f54,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) ) | ~spl2_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f77])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) | spl2_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f52])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    spl2_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f109])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl2_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f105])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl2_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f101])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl2_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f44,f93])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl2_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f43,f89])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl2_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f85])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl2_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f77])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl2_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f73])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl2_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f69])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl2_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f61])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f57])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ~spl2_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f52])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f20])).
% 0.22/0.53  fof(f20,conjecture,(
% 0.22/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (30105)------------------------------
% 0.22/0.53  % (30105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30105)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (30105)Memory used [KB]: 6524
% 0.22/0.53  % (30105)Time elapsed: 0.048 s
% 0.22/0.53  % (30105)------------------------------
% 0.22/0.53  % (30105)------------------------------
% 0.22/0.53  % (30099)Success in time 0.152 s
%------------------------------------------------------------------------------
