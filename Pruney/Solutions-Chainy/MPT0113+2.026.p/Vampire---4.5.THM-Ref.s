%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 168 expanded)
%              Number of leaves         :   30 (  80 expanded)
%              Depth                    :    8
%              Number of atoms          :  258 ( 406 expanded)
%              Number of equality atoms :   49 (  90 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f676,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f40,f44,f48,f52,f56,f60,f64,f68,f74,f88,f102,f134,f242,f302,f333,f345,f379,f578,f657,f675])).

fof(f675,plain,
    ( ~ spl3_1
    | ~ spl3_10
    | ~ spl3_11
    | spl3_12
    | ~ spl3_17
    | ~ spl3_29
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_44 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_11
    | spl3_12
    | ~ spl3_17
    | ~ spl3_29
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f87,f673])).

fof(f673,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_17
    | ~ spl3_29
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f672,f139])).

fof(f139,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK0)
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f137,f89])).

fof(f89,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f30,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f30,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f137,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0)
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(superposition,[],[f73,f133])).

fof(f133,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_17
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f73,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_11
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f672,plain,
    ( k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0)
    | ~ spl3_11
    | ~ spl3_29
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f664,f341])).

fof(f341,plain,
    ( ! [X8,X9] : k4_xboole_0(X8,X9) = k4_xboole_0(X8,k3_xboole_0(X8,X9))
    | ~ spl3_11
    | ~ spl3_29
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f338,f73])).

fof(f338,plain,
    ( ! [X8,X9] : k5_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,k3_xboole_0(X8,X9))
    | ~ spl3_29
    | ~ spl3_31 ),
    inference(superposition,[],[f332,f301])).

fof(f301,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl3_29
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f332,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl3_31
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f664,plain,
    ( k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_33
    | ~ spl3_44 ),
    inference(unit_resulting_resolution,[],[f656,f378])).

fof(f378,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl3_33
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f656,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl3_44
  <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f87,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_12
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f657,plain,
    ( spl3_44
    | ~ spl3_17
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f366,f343,f131,f654])).

fof(f343,plain,
    ( spl3_32
  <=> ! [X7,X8,X6] : r1_tarski(k3_xboole_0(X6,k4_xboole_0(X7,X8)),k3_xboole_0(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f366,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_17
    | ~ spl3_32 ),
    inference(superposition,[],[f344,f133])).

fof(f344,plain,
    ( ! [X6,X8,X7] : r1_tarski(k3_xboole_0(X6,k4_xboole_0(X7,X8)),k3_xboole_0(X6,X7))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f343])).

fof(f578,plain,
    ( spl3_3
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f251,f240,f131,f37])).

fof(f37,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f240,plain,
    ( spl3_26
  <=> ! [X9,X11,X10] : r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f251,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(superposition,[],[f241,f133])).

fof(f241,plain,
    ( ! [X10,X11,X9] : r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f240])).

fof(f379,plain,
    ( spl3_33
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f96,f72,f58,f377])).

fof(f58,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(superposition,[],[f73,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f58])).

% (5134)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f345,plain,
    ( spl3_32
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f109,f100,f46,f343])).

fof(f46,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f100,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f109,plain,
    ( ! [X6,X8,X7] : r1_tarski(k3_xboole_0(X6,k4_xboole_0(X7,X8)),k3_xboole_0(X6,X7))
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(superposition,[],[f47,f101])).

fof(f101,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f47,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f333,plain,
    ( spl3_31
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f97,f72,f54,f331])).

fof(f54,plain,
    ( spl3_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f97,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(superposition,[],[f73,f55])).

fof(f55,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f302,plain,
    ( spl3_29
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f77,f58,f50,f300])).

fof(f50,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f77,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f51,f59])).

fof(f51,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f242,plain,
    ( spl3_26
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f110,f100,f42,f240])).

fof(f42,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f110,plain,
    ( ! [X10,X11,X9] : r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11)
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(superposition,[],[f43,f101])).

fof(f43,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f134,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f75,f58,f28,f131])).

fof(f75,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f30,f59])).

fof(f102,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f26,f100])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f88,plain,
    ( ~ spl3_12
    | spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f83,f62,f33,f85])).

fof(f33,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f83,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_2
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f35,f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f35,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f74,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f22,f72])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f68,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f25,f66])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f64,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f24,f62])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f56,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f44,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f40,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f17,f37,f33])).

fof(f17,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f31,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:55:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (5124)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (5128)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (5130)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (5127)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (5122)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (5132)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (5126)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (5136)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (5135)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (5125)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (5123)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (5131)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (5137)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (5127)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f676,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f31,f40,f44,f48,f52,f56,f60,f64,f68,f74,f88,f102,f134,f242,f302,f333,f345,f379,f578,f657,f675])).
% 0.22/0.50  fof(f675,plain,(
% 0.22/0.50    ~spl3_1 | ~spl3_10 | ~spl3_11 | spl3_12 | ~spl3_17 | ~spl3_29 | ~spl3_31 | ~spl3_33 | ~spl3_44),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f674])).
% 0.22/0.50  fof(f674,plain,(
% 0.22/0.50    $false | (~spl3_1 | ~spl3_10 | ~spl3_11 | spl3_12 | ~spl3_17 | ~spl3_29 | ~spl3_31 | ~spl3_33 | ~spl3_44)),
% 0.22/0.50    inference(subsumption_resolution,[],[f87,f673])).
% 0.22/0.50  fof(f673,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_10 | ~spl3_11 | ~spl3_17 | ~spl3_29 | ~spl3_31 | ~spl3_33 | ~spl3_44)),
% 0.22/0.50    inference(forward_demodulation,[],[f672,f139])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    k1_xboole_0 = k5_xboole_0(sK0,sK0) | (~spl3_1 | ~spl3_10 | ~spl3_11 | ~spl3_17)),
% 0.22/0.50    inference(forward_demodulation,[],[f137,f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_10)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f30,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl3_10 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) | (~spl3_11 | ~spl3_17)),
% 0.22/0.50    inference(superposition,[],[f73,f133])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl3_17 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl3_11 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f672,plain,(
% 0.22/0.50    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0) | (~spl3_11 | ~spl3_29 | ~spl3_31 | ~spl3_33 | ~spl3_44)),
% 0.22/0.50    inference(forward_demodulation,[],[f664,f341])).
% 0.22/0.50  fof(f341,plain,(
% 0.22/0.50    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k4_xboole_0(X8,k3_xboole_0(X8,X9))) ) | (~spl3_11 | ~spl3_29 | ~spl3_31)),
% 0.22/0.50    inference(forward_demodulation,[],[f338,f73])).
% 0.22/0.50  fof(f338,plain,(
% 0.22/0.50    ( ! [X8,X9] : (k5_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,k3_xboole_0(X8,X9))) ) | (~spl3_29 | ~spl3_31)),
% 0.22/0.50    inference(superposition,[],[f332,f301])).
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) ) | ~spl3_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f300])).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    spl3_29 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.50  fof(f332,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | ~spl3_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f331])).
% 0.22/0.50  fof(f331,plain,(
% 0.22/0.50    spl3_31 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.50  fof(f664,plain,(
% 0.22/0.50    k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_33 | ~spl3_44)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f656,f378])).
% 0.22/0.50  fof(f378,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) ) | ~spl3_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f377])).
% 0.22/0.50  fof(f377,plain,(
% 0.22/0.50    spl3_33 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.50  fof(f656,plain,(
% 0.22/0.50    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_44),
% 0.22/0.50    inference(avatar_component_clause,[],[f654])).
% 0.22/0.50  fof(f654,plain,(
% 0.22/0.50    spl3_44 <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl3_12 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f657,plain,(
% 0.22/0.50    spl3_44 | ~spl3_17 | ~spl3_32),
% 0.22/0.50    inference(avatar_split_clause,[],[f366,f343,f131,f654])).
% 0.22/0.50  fof(f343,plain,(
% 0.22/0.50    spl3_32 <=> ! [X7,X8,X6] : r1_tarski(k3_xboole_0(X6,k4_xboole_0(X7,X8)),k3_xboole_0(X6,X7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.50  fof(f366,plain,(
% 0.22/0.50    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_17 | ~spl3_32)),
% 0.22/0.50    inference(superposition,[],[f344,f133])).
% 0.22/0.50  fof(f344,plain,(
% 0.22/0.50    ( ! [X6,X8,X7] : (r1_tarski(k3_xboole_0(X6,k4_xboole_0(X7,X8)),k3_xboole_0(X6,X7))) ) | ~spl3_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f343])).
% 0.22/0.50  fof(f578,plain,(
% 0.22/0.50    spl3_3 | ~spl3_17 | ~spl3_26),
% 0.22/0.50    inference(avatar_split_clause,[],[f251,f240,f131,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    spl3_26 <=> ! [X9,X11,X10] : r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    r1_xboole_0(sK0,sK2) | (~spl3_17 | ~spl3_26)),
% 0.22/0.50    inference(superposition,[],[f241,f133])).
% 0.22/0.50  fof(f241,plain,(
% 0.22/0.50    ( ! [X10,X11,X9] : (r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11)) ) | ~spl3_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f240])).
% 0.22/0.50  fof(f379,plain,(
% 0.22/0.50    spl3_33 | ~spl3_8 | ~spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f96,f72,f58,f377])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) ) | (~spl3_8 | ~spl3_11)),
% 0.22/0.50    inference(superposition,[],[f73,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f58])).
% 0.22/0.50  % (5134)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  fof(f345,plain,(
% 0.22/0.50    spl3_32 | ~spl3_5 | ~spl3_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f109,f100,f46,f343])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    spl3_5 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl3_13 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ( ! [X6,X8,X7] : (r1_tarski(k3_xboole_0(X6,k4_xboole_0(X7,X8)),k3_xboole_0(X6,X7))) ) | (~spl3_5 | ~spl3_13)),
% 0.22/0.50    inference(superposition,[],[f47,f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f100])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f46])).
% 0.22/0.50  fof(f333,plain,(
% 0.22/0.50    spl3_31 | ~spl3_7 | ~spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f97,f72,f54,f331])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    spl3_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | (~spl3_7 | ~spl3_11)),
% 0.22/0.50    inference(superposition,[],[f73,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f54])).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    spl3_29 | ~spl3_6 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f77,f58,f50,f300])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    spl3_6 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) ) | (~spl3_6 | ~spl3_8)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f51,f59])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f50])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    spl3_26 | ~spl3_4 | ~spl3_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f110,f100,f42,f240])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    spl3_4 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ( ! [X10,X11,X9] : (r1_xboole_0(k3_xboole_0(X9,k4_xboole_0(X10,X11)),X11)) ) | (~spl3_4 | ~spl3_13)),
% 0.22/0.50    inference(superposition,[],[f43,f101])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f42])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl3_17 | ~spl3_1 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f75,f58,f28,f131])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_8)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f30,f59])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl3_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f100])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ~spl3_12 | spl3_2 | ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f83,f62,f33,f85])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl3_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_2 | ~spl3_9)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f35,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f62])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ~r1_tarski(sK0,sK1) | spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f33])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f72])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f66])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f62])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f58])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f21,f54])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f20,f50])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f19,f46])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f18,f42])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ~spl3_2 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f17,f37,f33])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f16,f28])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (5127)------------------------------
% 0.22/0.50  % (5127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5127)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (5127)Memory used [KB]: 6524
% 0.22/0.50  % (5127)Time elapsed: 0.065 s
% 0.22/0.50  % (5127)------------------------------
% 0.22/0.50  % (5127)------------------------------
% 0.22/0.50  % (5121)Success in time 0.139 s
%------------------------------------------------------------------------------
