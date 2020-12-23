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
% DateTime   : Thu Dec  3 12:34:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 104 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  148 ( 212 expanded)
%              Number of equality atoms :   57 (  89 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f967,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f41,f45,f49,f56,f62,f66,f75,f92,f128,f252,f682,f934,f962])).

fof(f962,plain,
    ( spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_41
    | ~ spl9_48 ),
    inference(avatar_contradiction_clause,[],[f961])).

fof(f961,plain,
    ( $false
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_41
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f28,f960])).

fof(f960,plain,
    ( ! [X39,X47,X45,X43,X41,X46,X44,X42,X40] : k7_enumset1(X39,X40,X41,X42,X43,X44,X45,X46,X47) = k2_xboole_0(k1_enumset1(X39,X40,X41),k4_enumset1(X42,X43,X44,X45,X46,X47))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_41
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f959,f40])).

fof(f40,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl9_4
  <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f959,plain,
    ( ! [X39,X47,X45,X43,X41,X46,X44,X42,X40] : k7_enumset1(X39,X40,X41,X42,X43,X44,X45,X46,X47) = k2_xboole_0(k2_enumset1(X39,X39,X40,X41),k4_enumset1(X42,X43,X44,X45,X46,X47))
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_41
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f958,f48])).

fof(f48,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl9_6
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f958,plain,
    ( ! [X39,X47,X45,X43,X41,X46,X44,X42,X40] : k2_xboole_0(k3_enumset1(X39,X39,X39,X40,X41),k4_enumset1(X42,X43,X44,X45,X46,X47)) = k7_enumset1(X39,X40,X41,X42,X43,X44,X45,X46,X47)
    | ~ spl9_10
    | ~ spl9_41
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f950,f74])).

fof(f74,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl9_10
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f950,plain,
    ( ! [X39,X47,X45,X43,X41,X46,X44,X42,X40] : k2_xboole_0(k3_enumset1(X39,X39,X39,X40,X41),k4_enumset1(X42,X43,X44,X45,X46,X47)) = k2_xboole_0(k2_enumset1(X39,X40,X41,X42),k3_enumset1(X43,X44,X45,X46,X47))
    | ~ spl9_41
    | ~ spl9_48 ),
    inference(superposition,[],[f681,f933])).

fof(f933,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f932])).

fof(f932,plain,
    ( spl9_48
  <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f681,plain,
    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : k2_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X6,X7,X8,X9,X10),k4_enumset1(X0,X1,X2,X3,X4,X5))
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f680])).

fof(f680,plain,
    ( spl9_41
  <=> ! [X9,X1,X3,X5,X7,X8,X10,X0,X2,X4,X6] : k2_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X6,X7,X8,X9,X10),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f28,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl9_1
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f934,plain,
    ( spl9_48
    | ~ spl9_12
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f255,f250,f90,f932])).

fof(f90,plain,
    ( spl9_12
  <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f250,plain,
    ( spl9_27
  <=> ! [X1,X3,X2,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f255,plain,
    ( ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)
    | ~ spl9_12
    | ~ spl9_27 ),
    inference(superposition,[],[f251,f91])).

fof(f91,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f251,plain,
    ( ! [X4,X2,X3,X1] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X2,X3,X4))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f250])).

fof(f682,plain,
    ( spl9_41
    | ~ spl9_8
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f131,f126,f60,f680])).

fof(f60,plain,
    ( spl9_8
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f126,plain,
    ( spl9_16
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f131,plain,
    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : k2_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X6,X7,X8,X9,X10),k4_enumset1(X0,X1,X2,X3,X4,X5))
    | ~ spl9_8
    | ~ spl9_16 ),
    inference(superposition,[],[f127,f61])).

fof(f61,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f127,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f252,plain,
    ( spl9_27
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f100,f90,f54,f47,f250])).

fof(f54,plain,
    ( spl9_7
  <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f100,plain,
    ( ! [X4,X2,X3,X1] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X2,X3,X4))
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_12 ),
    inference(forward_demodulation,[],[f94,f48])).

fof(f94,plain,
    ( ! [X4,X2,X3,X1] : k3_enumset1(X1,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X2,X3,X4))
    | ~ spl9_7
    | ~ spl9_12 ),
    inference(superposition,[],[f91,f55])).

fof(f55,plain,
    ( ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f128,plain,
    ( spl9_16
    | ~ spl9_5
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f70,f64,f43,f126])).

fof(f43,plain,
    ( spl9_5
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f64,plain,
    ( spl9_9
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f70,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6))
    | ~ spl9_5
    | ~ spl9_9 ),
    inference(superposition,[],[f44,f65])).

fof(f65,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f44,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f92,plain,
    ( spl9_12
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f67,f60,f47,f90])).

fof(f67,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(superposition,[],[f61,f48])).

fof(f75,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f24,f73])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

fof(f66,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f23,f64])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f62,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f22,f60])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f56,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f41,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (14956)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (14958)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (14945)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (14955)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (14946)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (14947)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (14949)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (14953)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (14943)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (14948)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (14951)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (14959)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (14957)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (14954)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (14950)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (14944)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (14960)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (14954)Refutation not found, incomplete strategy% (14954)------------------------------
% 0.20/0.50  % (14954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (14954)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (14954)Memory used [KB]: 10618
% 0.20/0.50  % (14954)Time elapsed: 0.086 s
% 0.20/0.50  % (14954)------------------------------
% 0.20/0.50  % (14954)------------------------------
% 0.20/0.50  % (14952)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (14948)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f967,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f29,f41,f45,f49,f56,f62,f66,f75,f92,f128,f252,f682,f934,f962])).
% 0.20/0.52  fof(f962,plain,(
% 0.20/0.52    spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_10 | ~spl9_41 | ~spl9_48),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f961])).
% 0.20/0.52  fof(f961,plain,(
% 0.20/0.52    $false | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_10 | ~spl9_41 | ~spl9_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f28,f960])).
% 0.20/0.52  fof(f960,plain,(
% 0.20/0.52    ( ! [X39,X47,X45,X43,X41,X46,X44,X42,X40] : (k7_enumset1(X39,X40,X41,X42,X43,X44,X45,X46,X47) = k2_xboole_0(k1_enumset1(X39,X40,X41),k4_enumset1(X42,X43,X44,X45,X46,X47))) ) | (~spl9_4 | ~spl9_6 | ~spl9_10 | ~spl9_41 | ~spl9_48)),
% 0.20/0.52    inference(forward_demodulation,[],[f959,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) ) | ~spl9_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    spl9_4 <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.52  fof(f959,plain,(
% 0.20/0.52    ( ! [X39,X47,X45,X43,X41,X46,X44,X42,X40] : (k7_enumset1(X39,X40,X41,X42,X43,X44,X45,X46,X47) = k2_xboole_0(k2_enumset1(X39,X39,X40,X41),k4_enumset1(X42,X43,X44,X45,X46,X47))) ) | (~spl9_6 | ~spl9_10 | ~spl9_41 | ~spl9_48)),
% 0.20/0.52    inference(forward_demodulation,[],[f958,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) ) | ~spl9_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    spl9_6 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.20/0.52  fof(f958,plain,(
% 0.20/0.52    ( ! [X39,X47,X45,X43,X41,X46,X44,X42,X40] : (k2_xboole_0(k3_enumset1(X39,X39,X39,X40,X41),k4_enumset1(X42,X43,X44,X45,X46,X47)) = k7_enumset1(X39,X40,X41,X42,X43,X44,X45,X46,X47)) ) | (~spl9_10 | ~spl9_41 | ~spl9_48)),
% 0.20/0.52    inference(forward_demodulation,[],[f950,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) ) | ~spl9_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    spl9_10 <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.20/0.52  fof(f950,plain,(
% 0.20/0.52    ( ! [X39,X47,X45,X43,X41,X46,X44,X42,X40] : (k2_xboole_0(k3_enumset1(X39,X39,X39,X40,X41),k4_enumset1(X42,X43,X44,X45,X46,X47)) = k2_xboole_0(k2_enumset1(X39,X40,X41,X42),k3_enumset1(X43,X44,X45,X46,X47))) ) | (~spl9_41 | ~spl9_48)),
% 0.20/0.52    inference(superposition,[],[f681,f933])).
% 0.20/0.52  fof(f933,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) ) | ~spl9_48),
% 0.20/0.52    inference(avatar_component_clause,[],[f932])).
% 0.20/0.52  fof(f932,plain,(
% 0.20/0.52    spl9_48 <=> ! [X1,X3,X0,X2] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 0.20/0.52  fof(f681,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (k2_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X6,X7,X8,X9,X10),k4_enumset1(X0,X1,X2,X3,X4,X5))) ) | ~spl9_41),
% 0.20/0.52    inference(avatar_component_clause,[],[f680])).
% 0.20/0.52  fof(f680,plain,(
% 0.20/0.52    spl9_41 <=> ! [X9,X1,X3,X5,X7,X8,X10,X0,X2,X4,X6] : k2_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X6,X7,X8,X9,X10),k4_enumset1(X0,X1,X2,X3,X4,X5))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) | spl9_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    spl9_1 <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.52  fof(f934,plain,(
% 0.20/0.52    spl9_48 | ~spl9_12 | ~spl9_27),
% 0.20/0.52    inference(avatar_split_clause,[],[f255,f250,f90,f932])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    spl9_12 <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.20/0.52  fof(f250,plain,(
% 0.20/0.52    spl9_27 <=> ! [X1,X3,X2,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.20/0.52  fof(f255,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) ) | (~spl9_12 | ~spl9_27)),
% 0.20/0.52    inference(superposition,[],[f251,f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) ) | ~spl9_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f90])).
% 0.20/0.52  fof(f251,plain,(
% 0.20/0.52    ( ! [X4,X2,X3,X1] : (k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X2,X3,X4))) ) | ~spl9_27),
% 0.20/0.52    inference(avatar_component_clause,[],[f250])).
% 0.20/0.52  fof(f682,plain,(
% 0.20/0.52    spl9_41 | ~spl9_8 | ~spl9_16),
% 0.20/0.52    inference(avatar_split_clause,[],[f131,f126,f60,f680])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    spl9_8 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    spl9_16 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (k2_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X6,X7,X8,X9,X10),k4_enumset1(X0,X1,X2,X3,X4,X5))) ) | (~spl9_8 | ~spl9_16)),
% 0.20/0.52    inference(superposition,[],[f127,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) ) | ~spl9_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f60])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6))) ) | ~spl9_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f126])).
% 0.20/0.52  fof(f252,plain,(
% 0.20/0.52    spl9_27 | ~spl9_6 | ~spl9_7 | ~spl9_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f100,f90,f54,f47,f250])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    spl9_7 <=> ! [X1,X3,X0,X2,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    ( ! [X4,X2,X3,X1] : (k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X2,X3,X4))) ) | (~spl9_6 | ~spl9_7 | ~spl9_12)),
% 0.20/0.52    inference(forward_demodulation,[],[f94,f48])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ( ! [X4,X2,X3,X1] : (k3_enumset1(X1,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X2,X3,X4))) ) | (~spl9_7 | ~spl9_12)),
% 0.20/0.52    inference(superposition,[],[f91,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) ) | ~spl9_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f54])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    spl9_16 | ~spl9_5 | ~spl9_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f70,f64,f43,f126])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    spl9_5 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    spl9_9 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_xboole_0(k1_tarski(X5),X6))) ) | (~spl9_5 | ~spl9_9)),
% 0.20/0.52    inference(superposition,[],[f44,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) ) | ~spl9_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f64])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl9_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f43])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    spl9_12 | ~spl9_6 | ~spl9_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f67,f60,f47,f90])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) ) | (~spl9_6 | ~spl9_8)),
% 0.20/0.52    inference(superposition,[],[f61,f48])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    spl9_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f24,f73])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    spl9_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f23,f64])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    spl9_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f22,f60])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    spl9_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f21,f54])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    spl9_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f20,f47])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    spl9_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f19,f43])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    spl9_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f18,f39])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ~spl9_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f15,f26])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f12,f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_enumset1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (14948)------------------------------
% 0.20/0.52  % (14948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14948)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (14948)Memory used [KB]: 6908
% 0.20/0.52  % (14948)Time elapsed: 0.107 s
% 0.20/0.52  % (14948)------------------------------
% 0.20/0.52  % (14948)------------------------------
% 0.20/0.52  % (14942)Success in time 0.164 s
%------------------------------------------------------------------------------
