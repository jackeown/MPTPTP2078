%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0329+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:24 EST 2020

% Result     : Theorem 46.02s
% Output     : Refutation 46.33s
% Verified   : 
% Statistics : Number of formulae       :  577 (3427 expanded)
%              Number of leaves         :   76 (1222 expanded)
%              Depth                    :   36
%              Number of atoms          : 1390 (4935 expanded)
%              Number of equality atoms :  584 (3274 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31067,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1280,f1430,f1435,f1441,f1673,f1710,f1716,f2351,f3725,f5006,f5024,f5029,f5047,f5075,f6359,f6452,f6454,f6543,f6644,f7901,f7906,f19673,f22661,f23995,f25269,f26389,f27945,f27958,f30666,f30783,f31066])).

fof(f31066,plain,
    ( ~ spl18_4
    | spl18_9
    | ~ spl18_17
    | spl18_20
    | ~ spl18_40 ),
    inference(avatar_contradiction_clause,[],[f31065])).

fof(f31065,plain,
    ( $false
    | ~ spl18_4
    | spl18_9
    | ~ spl18_17
    | spl18_20
    | ~ spl18_40 ),
    inference(subsumption_resolution,[],[f31064,f1715])).

fof(f1715,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl18_9 ),
    inference(avatar_component_clause,[],[f1713])).

fof(f1713,plain,
    ( spl18_9
  <=> sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_9])])).

fof(f31064,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl18_4
    | ~ spl18_17
    | spl18_20
    | ~ spl18_40 ),
    inference(forward_demodulation,[],[f31063,f635])).

fof(f635,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f31063,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_xboole_0))
    | ~ spl18_4
    | ~ spl18_17
    | spl18_20
    | ~ spl18_40 ),
    inference(forward_demodulation,[],[f31062,f1041])).

fof(f1041,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f882,f636])).

fof(f636,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f882,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f638,f742])).

fof(f742,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f638,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f31062,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK3,sK3)))
    | ~ spl18_4
    | ~ spl18_17
    | spl18_20
    | ~ spl18_40 ),
    inference(backward_demodulation,[],[f31057,f31061])).

fof(f31061,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK2))
    | spl18_20 ),
    inference(resolution,[],[f10263,f773])).

fof(f773,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f406])).

fof(f406,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f10263,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl18_20 ),
    inference(avatar_component_clause,[],[f10261])).

fof(f10261,plain,
    ( spl18_20
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_20])])).

fof(f31057,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK2)))))
    | ~ spl18_4
    | ~ spl18_17
    | ~ spl18_40 ),
    inference(forward_demodulation,[],[f30963,f31056])).

fof(f31056,plain,
    ( sK3 = k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))
    | ~ spl18_4
    | ~ spl18_17 ),
    inference(forward_demodulation,[],[f31055,f30999])).

fof(f30999,plain,
    ( ! [X23] : sK3 = k4_xboole_0(sK3,k4_xboole_0(X23,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30998,f1503])).

fof(f1503,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    inference(superposition,[],[f1395,f786])).

fof(f786,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1395,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(resolution,[],[f654,f781])).

fof(f781,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f654,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f484])).

fof(f484,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f30998,plain,
    ( ! [X23] : k4_xboole_0(sK3,k4_xboole_0(X23,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(sK3,k4_xboole_0(sK3,X23))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30997,f786])).

fof(f30997,plain,
    ( ! [X23] : k4_xboole_0(sK3,k4_xboole_0(X23,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(k4_xboole_0(sK3,X23),sK3)
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30903,f636])).

fof(f30903,plain,
    ( ! [X23] : k4_xboole_0(sK3,k4_xboole_0(X23,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(k4_xboole_0(sK3,X23),k4_xboole_0(sK3,k1_xboole_0))
    | ~ spl18_4 ),
    inference(superposition,[],[f922,f6640])).

fof(f6640,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | ~ spl18_4 ),
    inference(resolution,[],[f6462,f616])).

fof(f616,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f6462,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f6461,f859])).

fof(f859,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f574,f572,f572])).

fof(f572,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f574,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f6461,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f1428,f3628])).

fof(f3628,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f784,f786])).

fof(f784,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1428,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | ~ spl18_4 ),
    inference(avatar_component_clause,[],[f1427])).

fof(f1427,plain,
    ( spl18_4
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f922,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f723,f742])).

fof(f723,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f31055,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))
    | ~ spl18_4
    | ~ spl18_17 ),
    inference(forward_demodulation,[],[f31054,f766])).

fof(f766,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f31054,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | ~ spl18_4
    | ~ spl18_17 ),
    inference(forward_demodulation,[],[f31053,f922])).

fof(f31053,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK0))),k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))
    | ~ spl18_4
    | ~ spl18_17 ),
    inference(forward_demodulation,[],[f31052,f30679])).

fof(f30679,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),sK3)
    | ~ spl18_17 ),
    inference(resolution,[],[f3064,f654])).

fof(f3064,plain,
    ( r1_tarski(k1_tarski(sK0),sK3)
    | ~ spl18_17 ),
    inference(avatar_component_clause,[],[f3063])).

fof(f3063,plain,
    ( spl18_17
  <=> r1_tarski(k1_tarski(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_17])])).

fof(f31052,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK0))),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),sK3),k4_xboole_0(k2_xboole_0(k1_tarski(sK0),sK3),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30969,f943])).

fof(f943,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f745,f742,f742])).

fof(f745,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f30969,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK0))),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK0),sK3)))) = k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30968,f10734])).

fof(f10734,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k4_xboole_0(k2_xboole_0(X2,X4),k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f5673,f786])).

fof(f5673,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(backward_demodulation,[],[f920,f5672])).

fof(f5672,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X4,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X4),k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f5596,f1208])).

fof(f1208,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f786,f635])).

fof(f5596,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k2_xboole_0(X2,X4),k2_xboole_0(X2,X3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f765,f631])).

fof(f631,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f765,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f920,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f721,f742,f742])).

fof(f721,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f30968,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK0))),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK0),sK3)))) = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30877,f1208])).

fof(f30877,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK0))),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK0),sK3)))) = k4_xboole_0(k2_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3))))
    | ~ spl18_4 ),
    inference(superposition,[],[f7806,f6640])).

fof(f7806,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X1,X0)))) ),
    inference(backward_demodulation,[],[f5677,f7805])).

fof(f7805,plain,(
    ! [X14,X15,X13] : k2_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),k4_xboole_0(X13,k4_xboole_0(X13,X15))) = k4_xboole_0(X13,k4_xboole_0(X13,k2_xboole_0(X14,X15))) ),
    inference(forward_demodulation,[],[f7706,f766])).

fof(f7706,plain,(
    ! [X14,X15,X13] : k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X13,X14),X15)) = k2_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X13)),k4_xboole_0(X13,k4_xboole_0(X13,X15))) ),
    inference(superposition,[],[f922,f943])).

fof(f5677,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) ),
    inference(forward_demodulation,[],[f5675,f766])).

fof(f5675,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(backward_demodulation,[],[f3492,f5674])).

fof(f5674,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X7,k2_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X7),k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f5597,f1208])).

fof(f5597,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(X5,X7),k2_xboole_0(X6,X5)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,k2_xboole_0(X6,X5))) ),
    inference(superposition,[],[f765,f1211])).

fof(f1211,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f631,f786])).

fof(f3492,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X0))) ),
    inference(forward_demodulation,[],[f3491,f1503])).

fof(f3491,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) ),
    inference(backward_demodulation,[],[f1110,f3490])).

fof(f3490,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k2_xboole_0(X11,X12)) = k4_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f3429,f766])).

fof(f3429,plain,(
    ! [X12,X10,X11] : k4_xboole_0(k4_xboole_0(X10,X11),X12) = k4_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f766,f780])).

fof(f780,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1110,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)))))) ),
    inference(forward_demodulation,[],[f1108,f784])).

fof(f1108,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))))) ),
    inference(backward_demodulation,[],[f1093,f786])).

fof(f1093,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)))) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,k4_xboole_0(X2,X0)))) ),
    inference(backward_demodulation,[],[f1087,f784])).

fof(f1087,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)))) ),
    inference(backward_demodulation,[],[f1077,f1084])).

fof(f1084,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f930,f766])).

fof(f930,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f731,f742,f742])).

fof(f731,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f1077,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X0))))) ),
    inference(backward_demodulation,[],[f918,f930])).

fof(f918,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))),k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))),k2_xboole_0(X2,X0))) ),
    inference(definition_unfolding,[],[f719,f742,f742,f742,f742,f742])).

fof(f719,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).

fof(f30963,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK2)))))
    | ~ spl18_4
    | ~ spl18_17
    | ~ spl18_40 ),
    inference(forward_demodulation,[],[f30962,f786])).

fof(f30962,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK2)))),k1_tarski(sK0))
    | ~ spl18_4
    | ~ spl18_17
    | ~ spl18_40 ),
    inference(forward_demodulation,[],[f30961,f943])).

fof(f30961,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK2),sK3))),k1_tarski(sK0))
    | ~ spl18_4
    | ~ spl18_17
    | ~ spl18_40 ),
    inference(forward_demodulation,[],[f30960,f30819])).

fof(f30819,plain,
    ( ! [X3] : k4_xboole_0(k2_xboole_0(k1_tarski(sK1),X3),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),X3),sK3)) = k2_xboole_0(k1_tarski(sK1),k4_xboole_0(X3,k4_xboole_0(X3,sK3)))
    | ~ spl18_40 ),
    inference(resolution,[],[f30769,f915])).

fof(f915,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(k2_xboole_0(X0,X2),X1)) ) ),
    inference(definition_unfolding,[],[f716,f742,f742])).

fof(f716,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f503])).

fof(f503,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f90])).

fof(f90,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).

fof(f30769,plain,
    ( r1_tarski(k1_tarski(sK1),sK3)
    | ~ spl18_40 ),
    inference(resolution,[],[f19721,f1342])).

fof(f1342,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X5,X4),X6)
      | r1_tarski(X4,X6) ) ),
    inference(superposition,[],[f646,f786])).

fof(f646,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f479])).

fof(f479,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f19721,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3)
    | ~ spl18_40 ),
    inference(avatar_component_clause,[],[f19720])).

fof(f19720,plain,
    ( spl18_40
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_40])])).

fof(f30960,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),k1_tarski(sK0))
    | ~ spl18_4
    | ~ spl18_17 ),
    inference(forward_demodulation,[],[f30959,f1040])).

fof(f1040,plain,(
    ! [X0] : k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f858,f978])).

fof(f978,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(equality_resolution,[],[f867])).

fof(f867,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ) ),
    inference(definition_unfolding,[],[f593,f572])).

fof(f593,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f460])).

fof(f460,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f416])).

fof(f416,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f858,plain,(
    ! [X0,X1] : k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))) ),
    inference(definition_unfolding,[],[f573,f742,f572])).

fof(f573,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f360])).

fof(f360,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f30959,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),k4_xboole_0(k1_tarski(sK0),k1_xboole_0))
    | ~ spl18_4
    | ~ spl18_17 ),
    inference(forward_demodulation,[],[f30958,f30847])).

fof(f30847,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,X1))
    | ~ spl18_17 ),
    inference(resolution,[],[f30728,f612])).

fof(f612,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f409])).

fof(f409,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f30728,plain,
    ( ! [X0] : r2_hidden(sK0,k2_xboole_0(sK3,X0))
    | ~ spl18_17 ),
    inference(superposition,[],[f30674,f786])).

fof(f30674,plain,
    ( ! [X0] : r2_hidden(sK0,k2_xboole_0(X0,sK3))
    | ~ spl18_17 ),
    inference(resolution,[],[f3064,f1347])).

fof(f1347,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k1_tarski(X3),X4)
      | r2_hidden(X3,k2_xboole_0(X5,X4)) ) ),
    inference(resolution,[],[f648,f686])).

fof(f686,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f297])).

fof(f297,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f648,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f481])).

fof(f481,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f30958,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))) = k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30957,f10872])).

fof(f10872,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X8,X9)))) = k2_xboole_0(X8,k4_xboole_0(X10,k4_xboole_0(X10,X9))) ),
    inference(forward_demodulation,[],[f10736,f5673])).

fof(f10736,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X8,X9)))) = k4_xboole_0(k2_xboole_0(X8,X10),k4_xboole_0(X10,k2_xboole_0(X8,X9))) ),
    inference(superposition,[],[f5673,f785])).

fof(f785,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f137])).

fof(f137,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f30957,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))) = k2_xboole_0(sK3,k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30956,f18158])).

fof(f18158,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X8,X9)))) = k2_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f18157,f7828])).

fof(f7828,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = X2 ),
    inference(forward_demodulation,[],[f7827,f1503])).

fof(f7827,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(X2,k4_xboole_0(X2,X4)) ),
    inference(forward_demodulation,[],[f7826,f786])).

fof(f7826,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),X2) ),
    inference(forward_demodulation,[],[f7724,f636])).

fof(f7724,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f922,f631])).

fof(f18157,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X8,X9)))) ),
    inference(forward_demodulation,[],[f18156,f785])).

fof(f18156,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X8,k2_xboole_0(X8,X9))))) ),
    inference(forward_demodulation,[],[f18155,f786])).

fof(f18155,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X9,X10))) = k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X8,X9),X8)))) ),
    inference(forward_demodulation,[],[f18154,f10734])).

fof(f18154,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X8,X9),X8)))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,k2_xboole_0(X10,X8))) ),
    inference(forward_demodulation,[],[f18153,f635])).

fof(f18153,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X8,X9),X8)))) = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X8)),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f18152,f631])).

fof(f18152,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X8,X9),X8)))) = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X8)),k4_xboole_0(X8,k2_xboole_0(X8,k2_xboole_0(X9,X10))))) ),
    inference(forward_demodulation,[],[f18151,f784])).

fof(f18151,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X8,X9),X8)))) = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X8)),k4_xboole_0(X8,k2_xboole_0(k2_xboole_0(X8,X9),X10)))) ),
    inference(forward_demodulation,[],[f18150,f786])).

fof(f18150,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X8,X9),X8)))) = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(k4_xboole_0(X8,k2_xboole_0(k2_xboole_0(X8,X9),X10)),k4_xboole_0(X9,k2_xboole_0(X10,X8)))) ),
    inference(forward_demodulation,[],[f17898,f5674])).

fof(f17898,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))),k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(k2_xboole_0(X8,X9),X8)))) = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(k4_xboole_0(X8,k2_xboole_0(k2_xboole_0(X8,X9),X10)),k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X10,X8)))) ),
    inference(superposition,[],[f7806,f785])).

fof(f30956,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))) = k2_xboole_0(sK3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK0))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30955,f10711])).

fof(f10711,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_xboole_0(X3,X2),k4_xboole_0(X3,k2_xboole_0(X2,X4))) ),
    inference(superposition,[],[f5673,f786])).

fof(f30955,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(sK3,k1_tarski(sK0))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30954,f1208])).

fof(f30954,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3),k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(sK3,k1_tarski(sK0)))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f30876,f25671])).

fof(f25671,plain,(
    ! [X39,X41,X40] : k4_xboole_0(X39,k2_xboole_0(X40,X41)) = k4_xboole_0(X39,k2_xboole_0(X41,X40)) ),
    inference(forward_demodulation,[],[f25670,f24846])).

fof(f24846,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k4_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0) ),
    inference(forward_demodulation,[],[f24681,f1211])).

fof(f24681,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X7))) ),
    inference(superposition,[],[f4231,f2083])).

fof(f2083,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k2_xboole_0(X8,k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f2064,f779])).

fof(f779,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2064,plain,(
    ! [X8,X7] : k2_xboole_0(X8,k2_xboole_0(X7,X8)) = k2_xboole_0(X8,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f779,f780])).

fof(f4231,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = X13 ),
    inference(forward_demodulation,[],[f4230,f636])).

fof(f4230,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) = k4_xboole_0(X13,k1_xboole_0) ),
    inference(forward_demodulation,[],[f4126,f1211])).

fof(f4126,plain,(
    ! [X12,X13] : k4_xboole_0(X13,k4_xboole_0(X13,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X12,X13)) ),
    inference(superposition,[],[f943,f780])).

fof(f25670,plain,(
    ! [X39,X41,X40] : k4_xboole_0(X39,k2_xboole_0(X40,X41)) = k4_xboole_0(X39,k4_xboole_0(k2_xboole_0(X40,X41),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f25669,f6319])).

fof(f6319,plain,(
    ! [X28,X29,X27] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X27,X28),k2_xboole_0(X27,k2_xboole_0(X29,X28))) ),
    inference(superposition,[],[f631,f1091])).

fof(f1091,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f783,f784])).

fof(f783,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_1)).

fof(f25669,plain,(
    ! [X39,X41,X42,X40] : k4_xboole_0(X39,k2_xboole_0(X40,X41)) = k4_xboole_0(X39,k4_xboole_0(k2_xboole_0(X40,X41),k4_xboole_0(k2_xboole_0(X40,X41),k2_xboole_0(X40,k2_xboole_0(X42,X41))))) ),
    inference(forward_demodulation,[],[f25523,f943])).

fof(f25523,plain,(
    ! [X39,X41,X42,X40] : k4_xboole_0(X39,k2_xboole_0(X40,X41)) = k4_xboole_0(X39,k4_xboole_0(k2_xboole_0(X40,k2_xboole_0(X42,X41)),k4_xboole_0(k2_xboole_0(X40,k2_xboole_0(X42,X41)),k2_xboole_0(X40,X41)))) ),
    inference(resolution,[],[f6327,f1074])).

fof(f1074,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X0,X2) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(backward_demodulation,[],[f914,f922])).

fof(f914,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ) ),
    inference(definition_unfolding,[],[f715,f742])).

fof(f715,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(cnf_transformation,[],[f502])).

fof(f502,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f6327,plain,(
    ! [X61,X62,X60] : r1_tarski(k2_xboole_0(X60,X61),k2_xboole_0(X60,k2_xboole_0(X62,X61))) ),
    inference(superposition,[],[f655,f1091])).

fof(f655,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f30876,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3),k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(sK3,k1_tarski(sK0))),k1_xboole_0))
    | ~ spl18_4 ),
    inference(superposition,[],[f7806,f6640])).

fof(f30783,plain,
    ( spl18_19
    | ~ spl18_40 ),
    inference(avatar_contradiction_clause,[],[f30782])).

fof(f30782,plain,
    ( $false
    | spl18_19
    | ~ spl18_40 ),
    inference(subsumption_resolution,[],[f30766,f10259])).

fof(f10259,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl18_19 ),
    inference(avatar_component_clause,[],[f10257])).

fof(f10257,plain,
    ( spl18_19
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_19])])).

fof(f30766,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl18_40 ),
    inference(resolution,[],[f19721,f838])).

fof(f838,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f552,f572])).

fof(f552,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f381])).

fof(f381,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f30666,plain,
    ( spl18_1
    | spl18_3
    | ~ spl18_4
    | spl18_5
    | spl18_8
    | spl18_17 ),
    inference(avatar_contradiction_clause,[],[f30665])).

fof(f30665,plain,
    ( $false
    | spl18_1
    | spl18_3
    | ~ spl18_4
    | spl18_5
    | spl18_8
    | spl18_17 ),
    inference(subsumption_resolution,[],[f30664,f1275])).

fof(f1275,plain,
    ( k1_xboole_0 != sK3
    | spl18_1 ),
    inference(avatar_component_clause,[],[f1273])).

fof(f1273,plain,
    ( spl18_1
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f30664,plain,
    ( k1_xboole_0 = sK3
    | spl18_3
    | ~ spl18_4
    | spl18_5
    | spl18_8
    | spl18_17 ),
    inference(backward_demodulation,[],[f30644,f30663])).

fof(f30663,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK0))
    | spl18_3
    | ~ spl18_4
    | spl18_5
    | spl18_8
    | spl18_17 ),
    inference(subsumption_resolution,[],[f30662,f1709])).

fof(f1709,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | spl18_8 ),
    inference(avatar_component_clause,[],[f1707])).

fof(f1707,plain,
    ( spl18_8
  <=> sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_8])])).

fof(f30662,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK0))
    | spl18_3
    | ~ spl18_4
    | spl18_5
    | spl18_17 ),
    inference(forward_demodulation,[],[f30661,f30644])).

fof(f30661,plain,
    ( k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k4_xboole_0(sK3,k1_tarski(sK0))
    | k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK0))
    | spl18_3
    | ~ spl18_4
    | spl18_5
    | spl18_17 ),
    inference(subsumption_resolution,[],[f30660,f1425])).

fof(f1425,plain,
    ( sK3 != k1_tarski(sK2)
    | spl18_3 ),
    inference(avatar_component_clause,[],[f1423])).

fof(f1423,plain,
    ( spl18_3
  <=> sK3 = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f30660,plain,
    ( sK3 = k1_tarski(sK2)
    | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k4_xboole_0(sK3,k1_tarski(sK0))
    | k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl18_4
    | spl18_5
    | spl18_17 ),
    inference(forward_demodulation,[],[f30659,f30644])).

fof(f30659,plain,
    ( k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0))
    | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k4_xboole_0(sK3,k1_tarski(sK0))
    | k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl18_4
    | spl18_5
    | spl18_17 ),
    inference(subsumption_resolution,[],[f30653,f1434])).

fof(f1434,plain,
    ( sK3 != k1_tarski(sK1)
    | spl18_5 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f1432,plain,
    ( spl18_5
  <=> sK3 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f30653,plain,
    ( sK3 = k1_tarski(sK1)
    | k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0))
    | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k4_xboole_0(sK3,k1_tarski(sK0))
    | k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl18_4
    | spl18_17 ),
    inference(backward_demodulation,[],[f26436,f30644])).

fof(f26436,plain,
    ( k1_tarski(sK1) = k4_xboole_0(sK3,k1_tarski(sK0))
    | k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0))
    | k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k4_xboole_0(sK3,k1_tarski(sK0))
    | k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl18_4 ),
    inference(resolution,[],[f8094,f874])).

fof(f874,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f596,f572,f572])).

fof(f596,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f461])).

fof(f461,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f385])).

fof(f385,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f8094,plain,
    ( r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ spl18_4 ),
    inference(resolution,[],[f6462,f759])).

fof(f759,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f515])).

fof(f515,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f105])).

fof(f105,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f30644,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK0))
    | spl18_17 ),
    inference(resolution,[],[f30633,f773])).

fof(f30633,plain,
    ( ~ r2_hidden(sK0,sK3)
    | spl18_17 ),
    inference(resolution,[],[f3065,f685])).

fof(f685,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f297])).

fof(f3065,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK3)
    | spl18_17 ),
    inference(avatar_component_clause,[],[f3063])).

fof(f27958,plain,
    ( ~ spl18_4
    | spl18_6
    | spl18_15
    | ~ spl18_17
    | spl18_20 ),
    inference(avatar_contradiction_clause,[],[f27957])).

fof(f27957,plain,
    ( $false
    | ~ spl18_4
    | spl18_6
    | spl18_15
    | ~ spl18_17
    | spl18_20 ),
    inference(subsumption_resolution,[],[f27956,f1440])).

fof(f1440,plain,
    ( sK3 != k1_tarski(sK0)
    | spl18_6 ),
    inference(avatar_component_clause,[],[f1438])).

fof(f1438,plain,
    ( spl18_6
  <=> sK3 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).

fof(f27956,plain,
    ( sK3 = k1_tarski(sK0)
    | ~ spl18_4
    | spl18_15
    | ~ spl18_17
    | spl18_20 ),
    inference(backward_demodulation,[],[f15377,f27954])).

fof(f27954,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = X3
    | ~ spl18_4
    | spl18_15
    | spl18_20 ),
    inference(forward_demodulation,[],[f27953,f636])).

fof(f27953,plain,
    ( ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0)))
    | ~ spl18_4
    | spl18_15
    | spl18_20 ),
    inference(forward_demodulation,[],[f27952,f13360])).

fof(f13360,plain,(
    ! [X140,X138,X139] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(X140),k1_tarski(X139)),k2_xboole_0(k1_tarski(X138),k2_xboole_0(k1_tarski(X139),k1_tarski(X140)))) ),
    inference(superposition,[],[f1211,f1068])).

fof(f1068,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X0),k1_tarski(X2))) ),
    inference(forward_demodulation,[],[f896,f894])).

fof(f894,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f669,f810,f572])).

fof(f810,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f667,f572,f572])).

fof(f667,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f225])).

fof(f225,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(f669,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f227])).

fof(f227,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f896,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f671,f810,f810])).

fof(f671,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f283])).

fof(f283,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

fof(f27952,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))
    | ~ spl18_4
    | spl18_15
    | spl18_20 ),
    inference(backward_demodulation,[],[f27477,f27950])).

fof(f27950,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK3)
    | spl18_15 ),
    inference(resolution,[],[f27946,f1015])).

fof(f1015,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2) ) ),
    inference(forward_demodulation,[],[f968,f812])).

fof(f812,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f576,f572])).

fof(f576,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f968,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k1_tarski(X1) = k4_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X1)),X2) ) ),
    inference(equality_resolution,[],[f831])).

fof(f831,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | X0 != X1
      | k1_tarski(X0) = k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) ) ),
    inference(definition_unfolding,[],[f544,f572])).

fof(f544,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | X0 != X1
      | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f307])).

fof(f307,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f27946,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl18_15 ),
    inference(resolution,[],[f2937,f685])).

fof(f2937,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK3)
    | spl18_15 ),
    inference(avatar_component_clause,[],[f2935])).

fof(f2935,plain,
    ( spl18_15
  <=> r1_tarski(k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_15])])).

fof(f27477,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK1),sK3)))))
    | ~ spl18_4
    | spl18_20 ),
    inference(backward_demodulation,[],[f26453,f27475])).

fof(f27475,plain,
    ( ! [X11] : k4_xboole_0(k2_xboole_0(X11,k1_tarski(sK2)),sK3) = k2_xboole_0(k1_tarski(sK2),k4_xboole_0(X11,sK3))
    | spl18_20 ),
    inference(forward_demodulation,[],[f27411,f786])).

fof(f27411,plain,
    ( ! [X11] : k4_xboole_0(k2_xboole_0(X11,k1_tarski(sK2)),sK3) = k2_xboole_0(k4_xboole_0(X11,sK3),k1_tarski(sK2))
    | spl18_20 ),
    inference(superposition,[],[f765,f26456])).

fof(f26456,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)
    | spl18_20 ),
    inference(resolution,[],[f10263,f1015])).

fof(f26453,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f26452,f25671])).

fof(f26452,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3),k1_tarski(sK0))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f26445,f1084])).

fof(f26445,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(sK3,k1_tarski(sK0)))))
    | ~ spl18_4 ),
    inference(resolution,[],[f8094,f1074])).

fof(f15377,plain,
    ( k1_tarski(sK0) = k4_xboole_0(sK3,k4_xboole_0(sK3,k1_tarski(sK0)))
    | ~ spl18_17 ),
    inference(resolution,[],[f15267,f936])).

fof(f936,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) ) ),
    inference(definition_unfolding,[],[f737,f742])).

fof(f737,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f510])).

fof(f510,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f304])).

fof(f304,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f15267,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl18_17 ),
    inference(resolution,[],[f3064,f686])).

fof(f27945,plain,
    ( ~ spl18_15
    | ~ spl18_13
    | ~ spl18_4
    | ~ spl18_17
    | spl18_18 ),
    inference(avatar_split_clause,[],[f19314,f3711,f3063,f1427,f2885,f2935])).

fof(f2885,plain,
    ( spl18_13
  <=> r1_tarski(k1_tarski(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_13])])).

fof(f3711,plain,
    ( spl18_18
  <=> sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_18])])).

fof(f19314,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK3)
    | ~ r1_tarski(k1_tarski(sK1),sK3)
    | ~ spl18_4
    | ~ spl18_17
    | spl18_18 ),
    inference(resolution,[],[f19265,f644])).

fof(f644,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f476])).

fof(f476,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f475])).

fof(f475,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f161])).

fof(f161,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f19265,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | ~ spl18_4
    | ~ spl18_17
    | spl18_18 ),
    inference(subsumption_resolution,[],[f19264,f992])).

fof(f992,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f650])).

fof(f650,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f19264,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3)
    | ~ r1_tarski(sK3,sK3)
    | ~ spl18_4
    | ~ spl18_17
    | spl18_18 ),
    inference(resolution,[],[f16736,f644])).

fof(f16736,plain,
    ( ~ r1_tarski(k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)
    | ~ spl18_4
    | ~ spl18_17
    | spl18_18 ),
    inference(backward_demodulation,[],[f7897,f16731])).

fof(f16731,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ spl18_4
    | ~ spl18_17 ),
    inference(backward_demodulation,[],[f6639,f16709])).

fof(f16709,plain,
    ( ! [X17] : k2_xboole_0(sK3,X17) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),X17))
    | ~ spl18_17 ),
    inference(superposition,[],[f784,f15667])).

fof(f15667,plain,
    ( sK3 = k2_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl18_17 ),
    inference(forward_demodulation,[],[f15614,f635])).

fof(f15614,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl18_17 ),
    inference(superposition,[],[f779,f15268])).

fof(f15268,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK3)
    | ~ spl18_17 ),
    inference(resolution,[],[f3064,f616])).

fof(f6639,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | ~ spl18_4 ),
    inference(resolution,[],[f6462,f654])).

fof(f7897,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)
    | ~ spl18_4
    | spl18_18 ),
    inference(subsumption_resolution,[],[f6637,f3712])).

fof(f3712,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl18_18 ),
    inference(avatar_component_clause,[],[f3711])).

fof(f6637,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ spl18_4 ),
    inference(resolution,[],[f6462,f651])).

fof(f651,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f26389,plain,
    ( ~ spl18_4
    | spl18_19
    | spl18_37 ),
    inference(avatar_contradiction_clause,[],[f26388])).

fof(f26388,plain,
    ( $false
    | ~ spl18_4
    | spl18_19
    | spl18_37 ),
    inference(subsumption_resolution,[],[f26377,f19668])).

fof(f19668,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | spl18_37 ),
    inference(avatar_component_clause,[],[f19666])).

fof(f19666,plain,
    ( spl18_37
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_37])])).

fof(f26377,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | ~ spl18_4
    | spl18_19 ),
    inference(resolution,[],[f25841,f758])).

fof(f758,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f514])).

fof(f514,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f106,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f25841,plain,
    ( r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK2))
    | ~ spl18_4
    | spl18_19 ),
    inference(backward_demodulation,[],[f24127,f25840])).

fof(f25840,plain,
    ( ! [X40] : k4_xboole_0(sK3,X40) = k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK1)))
    | spl18_19 ),
    inference(forward_demodulation,[],[f25839,f635])).

fof(f25839,plain,
    ( ! [X40] : k4_xboole_0(sK3,k2_xboole_0(X40,k1_xboole_0)) = k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK1)))
    | spl18_19 ),
    inference(forward_demodulation,[],[f25838,f766])).

fof(f25838,plain,
    ( ! [X40] : k4_xboole_0(k4_xboole_0(sK3,X40),k1_xboole_0) = k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK1)))
    | spl18_19 ),
    inference(forward_demodulation,[],[f25790,f1211])).

fof(f25790,plain,
    ( ! [X40] : k4_xboole_0(k4_xboole_0(sK3,X40),k4_xboole_0(sK3,k2_xboole_0(X40,sK3))) = k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK1)))
    | spl18_19 ),
    inference(superposition,[],[f1082,f25279])).

fof(f25279,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK1))
    | spl18_19 ),
    inference(resolution,[],[f10259,f773])).

fof(f1082,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2)))) ),
    inference(backward_demodulation,[],[f921,f766])).

fof(f921,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f722,f742])).

fof(f722,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f24127,plain,
    ( r1_tarski(k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f24116,f766])).

fof(f24116,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))
    | ~ spl18_4 ),
    inference(resolution,[],[f8094,f759])).

fof(f25269,plain,
    ( ~ spl18_19
    | ~ spl18_20
    | ~ spl18_4
    | ~ spl18_17
    | spl18_18 ),
    inference(avatar_split_clause,[],[f19313,f3711,f3063,f1427,f10261,f10257])).

fof(f19313,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK1,sK3)
    | ~ spl18_4
    | ~ spl18_17
    | spl18_18 ),
    inference(resolution,[],[f19265,f837])).

fof(f837,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f553,f572])).

fof(f553,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f381])).

fof(f23995,plain,
    ( ~ spl18_4
    | spl18_6
    | ~ spl18_17
    | spl18_38
    | spl18_40 ),
    inference(avatar_contradiction_clause,[],[f23994])).

fof(f23994,plain,
    ( $false
    | ~ spl18_4
    | spl18_6
    | ~ spl18_17
    | spl18_38
    | spl18_40 ),
    inference(subsumption_resolution,[],[f23993,f1440])).

fof(f23993,plain,
    ( sK3 = k1_tarski(sK0)
    | ~ spl18_4
    | spl18_6
    | ~ spl18_17
    | spl18_38
    | spl18_40 ),
    inference(backward_demodulation,[],[f23940,f23992])).

fof(f23992,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK2))
    | ~ spl18_17
    | spl18_38 ),
    inference(resolution,[],[f23987,f773])).

fof(f23987,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl18_17
    | spl18_38 ),
    inference(subsumption_resolution,[],[f23985,f15267])).

fof(f23985,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK0,sK3)
    | spl18_38 ),
    inference(resolution,[],[f19672,f837])).

fof(f19672,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)),sK3)
    | spl18_38 ),
    inference(avatar_component_clause,[],[f19670])).

fof(f19670,plain,
    ( spl18_38
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_38])])).

fof(f23940,plain,
    ( k1_tarski(sK0) = k4_xboole_0(sK3,k1_tarski(sK2))
    | ~ spl18_4
    | spl18_6
    | ~ spl18_17
    | spl18_40 ),
    inference(backward_demodulation,[],[f15377,f23938])).

fof(f23938,plain,
    ( k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl18_4
    | spl18_6
    | ~ spl18_17
    | spl18_40 ),
    inference(subsumption_resolution,[],[f23926,f15666])).

fof(f15666,plain,
    ( k1_xboole_0 != k4_xboole_0(sK3,k1_tarski(sK0))
    | spl18_6
    | ~ spl18_17 ),
    inference(subsumption_resolution,[],[f15612,f1440])).

fof(f15612,plain,
    ( k1_xboole_0 != k4_xboole_0(sK3,k1_tarski(sK0))
    | sK3 = k1_tarski(sK0)
    | ~ spl18_17 ),
    inference(superposition,[],[f775,f15268])).

fof(f775,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f523])).

fof(f523,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f92])).

fof(f92,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f23926,plain,
    ( k1_tarski(sK2) = k4_xboole_0(sK3,k1_tarski(sK0))
    | k1_xboole_0 = k4_xboole_0(sK3,k1_tarski(sK0))
    | ~ spl18_4
    | ~ spl18_17
    | spl18_40 ),
    inference(resolution,[],[f23100,f620])).

fof(f620,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f308])).

fof(f308,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f23100,plain,
    ( r1_tarski(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK2))
    | ~ spl18_4
    | ~ spl18_17
    | spl18_40 ),
    inference(backward_demodulation,[],[f19303,f23099])).

fof(f23099,plain,
    ( ! [X40] : k4_xboole_0(sK3,X40) = k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK1)))
    | ~ spl18_17
    | spl18_40 ),
    inference(forward_demodulation,[],[f23098,f635])).

fof(f23098,plain,
    ( ! [X40] : k4_xboole_0(sK3,k2_xboole_0(X40,k1_xboole_0)) = k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK1)))
    | ~ spl18_17
    | spl18_40 ),
    inference(forward_demodulation,[],[f23097,f766])).

fof(f23097,plain,
    ( ! [X40] : k4_xboole_0(k4_xboole_0(sK3,X40),k1_xboole_0) = k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK1)))
    | ~ spl18_17
    | spl18_40 ),
    inference(forward_demodulation,[],[f23056,f1211])).

fof(f23056,plain,
    ( ! [X40] : k4_xboole_0(k4_xboole_0(sK3,X40),k4_xboole_0(sK3,k2_xboole_0(X40,sK3))) = k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK1)))
    | ~ spl18_17
    | spl18_40 ),
    inference(superposition,[],[f1082,f22648])).

fof(f22648,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK1))
    | ~ spl18_17
    | spl18_40 ),
    inference(resolution,[],[f22643,f773])).

fof(f22643,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl18_17
    | spl18_40 ),
    inference(subsumption_resolution,[],[f22641,f15267])).

fof(f22641,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK0,sK3)
    | spl18_40 ),
    inference(resolution,[],[f19722,f837])).

fof(f19722,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK3)
    | spl18_40 ),
    inference(avatar_component_clause,[],[f19720])).

fof(f19303,plain,
    ( r1_tarski(k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK2))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f19292,f766])).

fof(f19292,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK3,k1_tarski(sK0)),k1_tarski(sK1)),k1_tarski(sK2))
    | ~ spl18_4 ),
    inference(resolution,[],[f8094,f759])).

fof(f22661,plain,
    ( ~ spl18_4
    | spl18_6
    | spl18_13
    | ~ spl18_17
    | spl18_40 ),
    inference(avatar_contradiction_clause,[],[f22660])).

fof(f22660,plain,
    ( $false
    | ~ spl18_4
    | spl18_6
    | spl18_13
    | ~ spl18_17
    | spl18_40 ),
    inference(subsumption_resolution,[],[f22659,f1440])).

fof(f22659,plain,
    ( sK3 = k1_tarski(sK0)
    | ~ spl18_4
    | spl18_13
    | ~ spl18_17
    | spl18_40 ),
    inference(backward_demodulation,[],[f15377,f22658])).

fof(f22658,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = X3
    | ~ spl18_4
    | spl18_13
    | ~ spl18_17
    | spl18_40 ),
    inference(forward_demodulation,[],[f22657,f636])).

fof(f22657,plain,
    ( ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0)))
    | ~ spl18_4
    | spl18_13
    | ~ spl18_17
    | spl18_40 ),
    inference(forward_demodulation,[],[f22652,f1211])).

fof(f22652,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),sK3)))
    | ~ spl18_4
    | spl18_13
    | ~ spl18_17
    | spl18_40 ),
    inference(backward_demodulation,[],[f19311,f22648])).

fof(f19311,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK3,k1_tarski(sK1)))))
    | ~ spl18_4
    | spl18_13 ),
    inference(forward_demodulation,[],[f19310,f16155])).

fof(f16155,plain,
    ( ! [X40] : k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK2))) = k4_xboole_0(sK3,X40)
    | spl18_13 ),
    inference(forward_demodulation,[],[f16154,f635])).

fof(f16154,plain,
    ( ! [X40] : k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK2))) = k4_xboole_0(sK3,k2_xboole_0(X40,k1_xboole_0))
    | spl18_13 ),
    inference(forward_demodulation,[],[f16153,f766])).

fof(f16153,plain,
    ( ! [X40] : k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK2))) = k4_xboole_0(k4_xboole_0(sK3,X40),k1_xboole_0)
    | spl18_13 ),
    inference(forward_demodulation,[],[f16119,f1211])).

fof(f16119,plain,
    ( ! [X40] : k4_xboole_0(sK3,k2_xboole_0(X40,k1_tarski(sK2))) = k4_xboole_0(k4_xboole_0(sK3,X40),k4_xboole_0(sK3,k2_xboole_0(X40,sK3)))
    | spl18_13 ),
    inference(superposition,[],[f1082,f15070])).

fof(f15070,plain,
    ( sK3 = k4_xboole_0(sK3,k1_tarski(sK2))
    | spl18_13 ),
    inference(resolution,[],[f15065,f773])).

fof(f15065,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl18_13 ),
    inference(resolution,[],[f2887,f685])).

fof(f2887,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK3)
    | spl18_13 ),
    inference(avatar_component_clause,[],[f2885])).

fof(f19310,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f19309,f8666])).

fof(f8666,plain,(
    ! [X28,X29,X27] : k4_xboole_0(X29,k2_xboole_0(k4_xboole_0(X29,X27),X28)) = k4_xboole_0(X29,k2_xboole_0(X28,k4_xboole_0(X29,X27))) ),
    inference(forward_demodulation,[],[f8665,f3455])).

fof(f3455,plain,(
    ! [X41,X42,X40] : k2_xboole_0(X42,k4_xboole_0(X40,X41)) = k2_xboole_0(X42,k4_xboole_0(X40,k2_xboole_0(X41,X42))) ),
    inference(superposition,[],[f779,f766])).

fof(f8665,plain,(
    ! [X28,X29,X27] : k4_xboole_0(X29,k2_xboole_0(k4_xboole_0(X29,X27),X28)) = k4_xboole_0(X29,k2_xboole_0(X28,k4_xboole_0(X29,k2_xboole_0(X27,X28)))) ),
    inference(forward_demodulation,[],[f8664,f786])).

fof(f8664,plain,(
    ! [X28,X29,X27] : k4_xboole_0(X29,k2_xboole_0(k4_xboole_0(X29,k2_xboole_0(X27,X28)),X28)) = k4_xboole_0(X29,k2_xboole_0(k4_xboole_0(X29,X27),X28)) ),
    inference(forward_demodulation,[],[f8550,f1084])).

fof(f8550,plain,(
    ! [X28,X29,X27] : k4_xboole_0(X29,k2_xboole_0(k4_xboole_0(X29,k2_xboole_0(X27,X28)),X28)) = k4_xboole_0(X29,k4_xboole_0(X29,k4_xboole_0(X27,X28))) ),
    inference(superposition,[],[f1084,f780])).

fof(f19309,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK0))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f19308,f766])).

fof(f19308,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k1_tarski(sK0)))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f19307,f4162])).

fof(f4162,plain,(
    ! [X47,X48,X49] : k4_xboole_0(X47,k2_xboole_0(k4_xboole_0(X47,X48),X49)) = k4_xboole_0(k4_xboole_0(X48,k4_xboole_0(X48,X47)),X49) ),
    inference(superposition,[],[f766,f943])).

fof(f19307,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),sK3),k1_tarski(sK0))))
    | ~ spl18_4 ),
    inference(forward_demodulation,[],[f19300,f1084])).

fof(f19300,plain,
    ( ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK3,k1_tarski(sK0))) = k4_xboole_0(X3,k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k4_xboole_0(sK3,k1_tarski(sK0)))))
    | ~ spl18_4 ),
    inference(resolution,[],[f8094,f1074])).

fof(f19673,plain,
    ( ~ spl18_37
    | ~ spl18_38
    | spl18_7 ),
    inference(avatar_split_clause,[],[f6492,f1670,f19670,f19666])).

fof(f1670,plain,
    ( spl18_7
  <=> sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).

fof(f6492,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)),sK3)
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | spl18_7 ),
    inference(extensionality_resolution,[],[f651,f1672])).

fof(f1672,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | spl18_7 ),
    inference(avatar_component_clause,[],[f1670])).

fof(f7906,plain,
    ( spl18_2
    | ~ spl18_4 ),
    inference(avatar_contradiction_clause,[],[f7905])).

fof(f7905,plain,
    ( $false
    | spl18_2
    | ~ spl18_4 ),
    inference(subsumption_resolution,[],[f7904,f6462])).

fof(f7904,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl18_2 ),
    inference(forward_demodulation,[],[f7903,f859])).

fof(f7903,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))
    | spl18_2 ),
    inference(forward_demodulation,[],[f7902,f1067])).

fof(f1067,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) ),
    inference(forward_demodulation,[],[f1066,f894])).

fof(f1066,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) ),
    inference(forward_demodulation,[],[f1065,f1064])).

fof(f1064,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) ),
    inference(forward_demodulation,[],[f1063,f1053])).

fof(f1053,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(backward_demodulation,[],[f893,f894])).

fof(f893,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f668,f810,f572])).

fof(f668,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f228])).

fof(f228,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f1063,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)) ),
    inference(backward_demodulation,[],[f1052,f1053])).

fof(f1052,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))) ),
    inference(forward_demodulation,[],[f1046,f893])).

fof(f1046,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X1)),k2_xboole_0(k1_tarski(X3),k1_tarski(X1)))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(backward_demodulation,[],[f891,f893])).

fof(f891,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))),k1_tarski(X3)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X1)),k2_xboole_0(k1_tarski(X3),k1_tarski(X1)))) ),
    inference(definition_unfolding,[],[f665,f811,f810])).

fof(f811,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f664,f810])).

fof(f664,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f231])).

fof(f231,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f665,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f229])).

fof(f229,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f1065,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f895,f894])).

fof(f895,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X0)),k2_xboole_0(k1_tarski(X1),k1_tarski(X0))),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f670,f810,f811])).

fof(f670,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f256])).

fof(f256,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f7902,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))
    | spl18_2 ),
    inference(forward_demodulation,[],[f1279,f1406])).

fof(f1406,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X0),k1_tarski(X2)))) ),
    inference(backward_demodulation,[],[f1158,f1401])).

fof(f1401,plain,(
    ! [X17,X15,X16] : k2_xboole_0(X16,k2_xboole_0(X15,X17)) = k2_xboole_0(X15,k2_xboole_0(X16,k2_xboole_0(X15,X17))) ),
    inference(resolution,[],[f654,f1339])).

fof(f1339,plain,(
    ! [X6,X7,X5] : r1_tarski(X5,k2_xboole_0(X6,k2_xboole_0(X5,X7))) ),
    inference(resolution,[],[f646,f1212])).

fof(f1212,plain,(
    ! [X4,X3] : r1_tarski(X3,k2_xboole_0(X4,X3)) ),
    inference(superposition,[],[f655,f786])).

fof(f1158,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X0),k1_tarski(X2))))) ),
    inference(forward_demodulation,[],[f1157,f1064])).

fof(f1157,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X0),k1_tarski(X2))))) ),
    inference(forward_demodulation,[],[f1156,f894])).

fof(f1156,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))),k1_tarski(X3)) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X0),k1_tarski(X2))))) ),
    inference(forward_demodulation,[],[f1155,f1053])).

fof(f1155,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))),k1_tarski(X3)) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X0)),k1_tarski(X2)))) ),
    inference(forward_demodulation,[],[f1154,f784])).

fof(f1154,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))),k1_tarski(X3)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X0)),k1_tarski(X2))) ),
    inference(forward_demodulation,[],[f961,f784])).

fof(f961,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X2),k1_tarski(X0))),k1_tarski(X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X0)),k2_xboole_0(k1_tarski(X3),k1_tarski(X0))),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f803,f811,f811])).

fof(f803,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f199])).

fof(f199,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f1279,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | spl18_2 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f1277,plain,
    ( spl18_2
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f7901,plain,
    ( ~ spl18_4
    | spl18_11 ),
    inference(avatar_contradiction_clause,[],[f7900])).

fof(f7900,plain,
    ( $false
    | ~ spl18_4
    | spl18_11 ),
    inference(subsumption_resolution,[],[f2350,f6462])).

fof(f2350,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl18_11 ),
    inference(avatar_component_clause,[],[f2348])).

fof(f2348,plain,
    ( spl18_11
  <=> r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_11])])).

fof(f6644,plain,
    ( spl18_11
    | spl18_18
    | spl18_1
    | spl18_3
    | spl18_5
    | spl18_6
    | spl18_7
    | spl18_8
    | spl18_9 ),
    inference(avatar_split_clause,[],[f6547,f1713,f1707,f1670,f1438,f1432,f1423,f1273,f3711,f2348])).

fof(f6547,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl18_1
    | spl18_3
    | spl18_5
    | spl18_6
    | spl18_7
    | spl18_8
    | spl18_9 ),
    inference(subsumption_resolution,[],[f6470,f1275])).

fof(f6470,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | k1_xboole_0 = sK3
    | spl18_3
    | spl18_5
    | spl18_6
    | spl18_7
    | spl18_8
    | spl18_9 ),
    inference(forward_demodulation,[],[f6469,f859])).

fof(f6469,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | k1_xboole_0 = sK3
    | spl18_3
    | spl18_5
    | spl18_6
    | spl18_7
    | spl18_8
    | spl18_9 ),
    inference(subsumption_resolution,[],[f6468,f1672])).

fof(f6468,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | k1_xboole_0 = sK3
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | spl18_3
    | spl18_5
    | spl18_6
    | spl18_8
    | spl18_9 ),
    inference(subsumption_resolution,[],[f6467,f1709])).

fof(f6467,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | k1_xboole_0 = sK3
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | spl18_3
    | spl18_5
    | spl18_6
    | spl18_9 ),
    inference(subsumption_resolution,[],[f6466,f1715])).

fof(f6466,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | k1_xboole_0 = sK3
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | spl18_3
    | spl18_5
    | spl18_6 ),
    inference(subsumption_resolution,[],[f6465,f1425])).

fof(f6465,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | spl18_5
    | spl18_6 ),
    inference(subsumption_resolution,[],[f6464,f1434])).

fof(f6464,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | spl18_6 ),
    inference(subsumption_resolution,[],[f3684,f1440])).

fof(f3684,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f1828,f3628])).

fof(f1828,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f1827,f859])).

fof(f1827,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f1826,f1067])).

fof(f1826,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f1413,f1406])).

fof(f1413,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f1105,f1401])).

fof(f1105,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f1096,f784])).

fof(f1096,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f1029,f784])).

fof(f1029,plain,
    ( r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f1028,f859])).

fof(f1028,plain,
    ( r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f1027,f859])).

fof(f1027,plain,
    ( sK3 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f1018,f859])).

fof(f1018,plain,
    ( sK3 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))
    | k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(backward_demodulation,[],[f813,f859])).

fof(f813,plain,
    ( k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | sK3 = k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))
    | r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f535,f572,f572,f572,f810,f810])).

fof(f535,plain,
    ( k1_xboole_0 = sK3
    | sK3 = k1_tarski(sK0)
    | sK3 = k1_tarski(sK1)
    | sK3 = k1_tarski(sK2)
    | sK3 = k2_tarski(sK0,sK1)
    | sK3 = k2_tarski(sK1,sK2)
    | sK3 = k2_tarski(sK0,sK2)
    | sK3 = k1_enumset1(sK0,sK1,sK2)
    | r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f438])).

fof(f438,plain,(
    ? [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <~> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f355])).

fof(f355,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      <=> ~ ( k1_enumset1(X0,X1,X2) != X3
            & k2_tarski(X0,X2) != X3
            & k2_tarski(X1,X2) != X3
            & k2_tarski(X0,X1) != X3
            & k1_tarski(X2) != X3
            & k1_tarski(X1) != X3
            & k1_tarski(X0) != X3
            & k1_xboole_0 != X3 ) ) ),
    inference(negated_conjecture,[],[f354])).

fof(f354,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f6543,plain,
    ( spl18_10
    | ~ spl18_18 ),
    inference(avatar_contradiction_clause,[],[f6542])).

fof(f6542,plain,
    ( $false
    | spl18_10
    | ~ spl18_18 ),
    inference(subsumption_resolution,[],[f6541,f992])).

fof(f6541,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl18_10
    | ~ spl18_18 ),
    inference(forward_demodulation,[],[f6540,f3713])).

fof(f3713,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | ~ spl18_18 ),
    inference(avatar_component_clause,[],[f3711])).

fof(f6540,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),sK3)
    | spl18_10
    | ~ spl18_18 ),
    inference(forward_demodulation,[],[f6539,f859])).

fof(f6539,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),sK3)
    | spl18_10
    | ~ spl18_18 ),
    inference(forward_demodulation,[],[f6538,f3628])).

fof(f6538,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),sK3)
    | spl18_10
    | ~ spl18_18 ),
    inference(subsumption_resolution,[],[f6537,f992])).

fof(f6537,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),sK3)
    | spl18_10
    | ~ spl18_18 ),
    inference(forward_demodulation,[],[f6536,f3713])).

fof(f6536,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),sK3)
    | spl18_10 ),
    inference(forward_demodulation,[],[f6535,f859])).

fof(f6535,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),sK3)
    | spl18_10 ),
    inference(forward_demodulation,[],[f6515,f3628])).

fof(f6515,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),sK3)
    | spl18_10 ),
    inference(extensionality_resolution,[],[f651,f2346])).

fof(f2346,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | spl18_10 ),
    inference(avatar_component_clause,[],[f2344])).

fof(f2344,plain,
    ( spl18_10
  <=> sK3 = k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_10])])).

fof(f6454,plain,
    ( spl18_4
    | ~ spl18_11 ),
    inference(avatar_contradiction_clause,[],[f6453])).

fof(f6453,plain,
    ( $false
    | spl18_4
    | ~ spl18_11 ),
    inference(subsumption_resolution,[],[f2349,f3722])).

fof(f3722,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl18_4 ),
    inference(forward_demodulation,[],[f3721,f859])).

fof(f3721,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))
    | spl18_4 ),
    inference(forward_demodulation,[],[f1429,f3628])).

fof(f1429,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | spl18_4 ),
    inference(avatar_component_clause,[],[f1427])).

fof(f2349,plain,
    ( r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | ~ spl18_11 ),
    inference(avatar_component_clause,[],[f2348])).

fof(f6452,plain,
    ( spl18_4
    | ~ spl18_9 ),
    inference(avatar_contradiction_clause,[],[f6451])).

fof(f6451,plain,
    ( $false
    | spl18_4
    | ~ spl18_9 ),
    inference(subsumption_resolution,[],[f6449,f655])).

fof(f6449,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK2)))
    | spl18_4
    | ~ spl18_9 ),
    inference(backward_demodulation,[],[f3722,f6424])).

fof(f6424,plain,
    ( ! [X27] : k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X27)) = k2_xboole_0(sK3,X27)
    | ~ spl18_9 ),
    inference(superposition,[],[f784,f1714])).

fof(f1714,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl18_9 ),
    inference(avatar_component_clause,[],[f1713])).

fof(f6359,plain,
    ( spl18_4
    | ~ spl18_7 ),
    inference(avatar_contradiction_clause,[],[f6358])).

fof(f6358,plain,
    ( $false
    | spl18_4
    | ~ spl18_7 ),
    inference(subsumption_resolution,[],[f6356,f655])).

fof(f6356,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | spl18_4
    | ~ spl18_7 ),
    inference(backward_demodulation,[],[f3722,f6284])).

fof(f6284,plain,
    ( ! [X50] : k2_xboole_0(k1_tarski(sK0),k2_xboole_0(X50,k1_tarski(sK2))) = k2_xboole_0(sK3,k2_xboole_0(X50,k1_tarski(sK2)))
    | ~ spl18_7 ),
    inference(superposition,[],[f1091,f1671])).

fof(f1671,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | ~ spl18_7 ),
    inference(avatar_component_clause,[],[f1670])).

fof(f5075,plain,
    ( spl18_4
    | ~ spl18_5 ),
    inference(avatar_contradiction_clause,[],[f5074])).

fof(f5074,plain,
    ( $false
    | spl18_4
    | ~ spl18_5 ),
    inference(subsumption_resolution,[],[f5062,f655])).

fof(f5062,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK3,k1_tarski(sK2)))
    | spl18_4
    | ~ spl18_5 ),
    inference(backward_demodulation,[],[f3798,f1433])).

fof(f1433,plain,
    ( sK3 = k1_tarski(sK1)
    | ~ spl18_5 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f3798,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))
    | spl18_4 ),
    inference(resolution,[],[f3722,f648])).

fof(f5047,plain,
    ( spl18_4
    | ~ spl18_6 ),
    inference(avatar_contradiction_clause,[],[f5046])).

fof(f5046,plain,
    ( $false
    | spl18_4
    | ~ spl18_6 ),
    inference(subsumption_resolution,[],[f5038,f992])).

fof(f5038,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl18_4
    | ~ spl18_6 ),
    inference(backward_demodulation,[],[f3797,f1439])).

fof(f1439,plain,
    ( sK3 = k1_tarski(sK0)
    | ~ spl18_6 ),
    inference(avatar_component_clause,[],[f1438])).

fof(f3797,plain,
    ( ~ r1_tarski(sK3,k1_tarski(sK0))
    | spl18_4 ),
    inference(resolution,[],[f3722,f1351])).

fof(f1351,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(X6,k2_xboole_0(X5,X4))
      | ~ r1_tarski(X6,X5) ) ),
    inference(superposition,[],[f648,f786])).

fof(f5029,plain,
    ( spl18_4
    | ~ spl18_18 ),
    inference(avatar_contradiction_clause,[],[f5028])).

fof(f5028,plain,
    ( $false
    | spl18_4
    | ~ spl18_18 ),
    inference(subsumption_resolution,[],[f5027,f992])).

fof(f5027,plain,
    ( ~ r1_tarski(sK3,sK3)
    | spl18_4
    | ~ spl18_18 ),
    inference(backward_demodulation,[],[f3722,f3713])).

fof(f5024,plain,
    ( ~ spl18_3
    | spl18_4 ),
    inference(avatar_contradiction_clause,[],[f5023])).

fof(f5023,plain,
    ( $false
    | ~ spl18_3
    | spl18_4 ),
    inference(subsumption_resolution,[],[f5022,f1369])).

fof(f1369,plain,(
    ! [X6,X4,X5] : r1_tarski(X4,k2_xboole_0(X6,k2_xboole_0(X5,X4))) ),
    inference(superposition,[],[f1339,f786])).

fof(f5022,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),sK3)))
    | ~ spl18_3
    | spl18_4 ),
    inference(forward_demodulation,[],[f3722,f1424])).

fof(f1424,plain,
    ( sK3 = k1_tarski(sK2)
    | ~ spl18_3 ),
    inference(avatar_component_clause,[],[f1423])).

fof(f5006,plain,
    ( ~ spl18_1
    | spl18_4 ),
    inference(avatar_contradiction_clause,[],[f5005])).

fof(f5005,plain,
    ( $false
    | ~ spl18_1
    | spl18_4 ),
    inference(subsumption_resolution,[],[f4989,f1189])).

fof(f1189,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f1010,f1041])).

fof(f1010,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f750])).

fof(f750,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f405])).

fof(f405,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f4989,plain,
    ( r2_hidden(sK13(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),k1_xboole_0)
    | ~ spl18_1
    | spl18_4 ),
    inference(backward_demodulation,[],[f3799,f1274])).

fof(f1274,plain,
    ( k1_xboole_0 = sK3
    | ~ spl18_1 ),
    inference(avatar_component_clause,[],[f1273])).

fof(f3799,plain,
    ( r2_hidden(sK13(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)))),sK3)
    | spl18_4 ),
    inference(resolution,[],[f3722,f694])).

fof(f694,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK13(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f488])).

fof(f488,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f3725,plain,
    ( spl18_4
    | ~ spl18_8 ),
    inference(avatar_contradiction_clause,[],[f3724])).

fof(f3724,plain,
    ( $false
    | spl18_4
    | ~ spl18_8 ),
    inference(subsumption_resolution,[],[f3723,f1212])).

fof(f3723,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),sK3))
    | spl18_4
    | ~ spl18_8 ),
    inference(forward_demodulation,[],[f3722,f1708])).

fof(f1708,plain,
    ( sK3 = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | ~ spl18_8 ),
    inference(avatar_component_clause,[],[f1707])).

fof(f2351,plain,
    ( ~ spl18_10
    | ~ spl18_11 ),
    inference(avatar_split_clause,[],[f1421,f2348,f2344])).

fof(f1421,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))))
    | sK3 != k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f1420,f859])).

fof(f1420,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))
    | sK3 != k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f1419,f1067])).

fof(f1419,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))))
    | sK3 != k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f1414,f1406])).

fof(f1414,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))) ),
    inference(backward_demodulation,[],[f1106,f1401])).

fof(f1106,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | sK3 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))) ),
    inference(forward_demodulation,[],[f1097,f784])).

fof(f1097,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))) ),
    inference(backward_demodulation,[],[f1032,f784])).

fof(f1032,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f1031,f859])).

fof(f1031,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f1030,f859])).

fof(f1030,plain,
    ( sK3 != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f1019,f859])).

fof(f1019,plain,
    ( sK3 != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(backward_demodulation,[],[f814,f859])).

fof(f814,plain,
    ( sK3 != k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f534,f810,f810])).

fof(f534,plain,
    ( sK3 != k1_enumset1(sK0,sK1,sK2)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f438])).

fof(f1716,plain,
    ( ~ spl18_9
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f1409,f1427,f1713])).

fof(f1409,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f1100,f1401])).

fof(f1100,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f1035,f784])).

fof(f1035,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f1022,f859])).

fof(f1022,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))))
    | sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f817,f859])).

fof(f817,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f531,f572,f810])).

fof(f531,plain,
    ( sK3 != k2_tarski(sK0,sK1)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f438])).

fof(f1710,plain,
    ( ~ spl18_8
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f1408,f1427,f1707])).

fof(f1408,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f1099,f1401])).

fof(f1099,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | sK3 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f1034,f784])).

fof(f1034,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f1021,f859])).

fof(f1021,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))))
    | sK3 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f816,f859])).

fof(f816,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f532,f572,f810])).

fof(f532,plain,
    ( sK3 != k2_tarski(sK1,sK2)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f438])).

fof(f1673,plain,
    ( ~ spl18_7
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f1407,f1427,f1670])).

fof(f1407,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f1098,f1401])).

fof(f1098,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f1033,f784])).

fof(f1033,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f1020,f859])).

fof(f1020,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))))
    | sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f815,f859])).

fof(f815,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f533,f572,f810])).

fof(f533,plain,
    ( sK3 != k2_tarski(sK0,sK2)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f438])).

fof(f1441,plain,
    ( ~ spl18_6
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f1412,f1427,f1438])).

fof(f1412,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f1103,f1401])).

fof(f1103,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | sK3 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f1038,f784])).

fof(f1038,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f1025,f859])).

fof(f1025,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))))
    | sK3 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f820,f859])).

fof(f820,plain,
    ( sK3 != k1_tarski(sK0)
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f528,f810])).

fof(f528,plain,
    ( sK3 != k1_tarski(sK0)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f438])).

fof(f1435,plain,
    ( ~ spl18_5
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f1411,f1427,f1432])).

fof(f1411,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k1_tarski(sK1) ),
    inference(backward_demodulation,[],[f1102,f1401])).

fof(f1102,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | sK3 != k1_tarski(sK1) ),
    inference(backward_demodulation,[],[f1037,f784])).

fof(f1037,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k1_tarski(sK1) ),
    inference(forward_demodulation,[],[f1024,f859])).

fof(f1024,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))))
    | sK3 != k1_tarski(sK1) ),
    inference(backward_demodulation,[],[f819,f859])).

fof(f819,plain,
    ( sK3 != k1_tarski(sK1)
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f529,f810])).

fof(f529,plain,
    ( sK3 != k1_tarski(sK1)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f438])).

fof(f1430,plain,
    ( ~ spl18_3
    | ~ spl18_4 ),
    inference(avatar_split_clause,[],[f1410,f1427,f1423])).

fof(f1410,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k1_tarski(sK2) ),
    inference(backward_demodulation,[],[f1101,f1401])).

fof(f1101,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | sK3 != k1_tarski(sK2) ),
    inference(backward_demodulation,[],[f1036,f784])).

fof(f1036,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | sK3 != k1_tarski(sK2) ),
    inference(forward_demodulation,[],[f1023,f859])).

fof(f1023,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))))
    | sK3 != k1_tarski(sK2) ),
    inference(backward_demodulation,[],[f818,f859])).

fof(f818,plain,
    ( sK3 != k1_tarski(sK2)
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f530,f810])).

fof(f530,plain,
    ( sK3 != k1_tarski(sK2)
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f438])).

fof(f1280,plain,
    ( ~ spl18_1
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f1104,f1277,f1273])).

fof(f1104,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)))))
    | k1_xboole_0 != sK3 ),
    inference(backward_demodulation,[],[f1039,f784])).

fof(f1039,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2))))
    | k1_xboole_0 != sK3 ),
    inference(forward_demodulation,[],[f1026,f859])).

fof(f1026,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0))))
    | k1_xboole_0 != sK3 ),
    inference(backward_demodulation,[],[f821,f859])).

fof(f821,plain,
    ( k1_xboole_0 != sK3
    | ~ r1_tarski(sK3,k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f527,f810])).

fof(f527,plain,
    ( k1_xboole_0 != sK3
    | ~ r1_tarski(sK3,k1_enumset1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f438])).
%------------------------------------------------------------------------------
