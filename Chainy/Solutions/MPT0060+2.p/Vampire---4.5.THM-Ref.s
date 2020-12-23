%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0060+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:06 EST 2020

% Result     : Theorem 2.80s
% Output     : Refutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 215 expanded)
%              Number of leaves         :   20 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 245 expanded)
%              Number of equality atoms :   91 ( 214 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2921,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f213,f2885,f2920])).

fof(f2920,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f2919])).

fof(f2919,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f2918,f327])).

fof(f327,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f182,f161])).

fof(f161,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f182,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f2918,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(sK0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl5_2 ),
    inference(forward_demodulation,[],[f2917,f811])).

fof(f811,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f185,f187])).

fof(f187,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f185,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f2917,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK0)))
    | spl5_2 ),
    inference(forward_demodulation,[],[f2916,f842])).

fof(f842,plain,(
    ! [X21,X22,X20] : k2_xboole_0(X20,k2_xboole_0(X21,k4_xboole_0(X22,X20))) = k2_xboole_0(X20,k2_xboole_0(X21,X22)) ),
    inference(forward_demodulation,[],[f841,f185])).

fof(f841,plain,(
    ! [X21,X22,X20] : k2_xboole_0(k2_xboole_0(X20,X21),X22) = k2_xboole_0(X20,k2_xboole_0(X21,k4_xboole_0(X22,X20))) ),
    inference(forward_demodulation,[],[f816,f779])).

fof(f779,plain,(
    ! [X37,X38,X36] : k2_xboole_0(X38,k4_xboole_0(X36,X37)) = k2_xboole_0(X38,k4_xboole_0(X36,k2_xboole_0(X37,X38))) ),
    inference(superposition,[],[f179,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f179,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f816,plain,(
    ! [X21,X22,X20] : k2_xboole_0(k2_xboole_0(X20,X21),X22) = k2_xboole_0(X20,k2_xboole_0(X21,k4_xboole_0(X22,k2_xboole_0(X20,X21)))) ),
    inference(superposition,[],[f185,f179])).

fof(f2916,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f2915,f309])).

fof(f309,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f305,f182])).

fof(f305,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f180,f180])).

fof(f180,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2915,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f2914,f162])).

fof(f162,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2914,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(k4_xboole_0(sK0,sK1),sK0))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f2913,f742])).

fof(f742,plain,(
    ! [X37,X38,X36] : k2_xboole_0(X38,k3_xboole_0(X36,X37)) = k2_xboole_0(X38,k3_xboole_0(X36,k4_xboole_0(X37,X38))) ),
    inference(superposition,[],[f179,f174])).

fof(f174,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f2913,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))))
    | spl5_2 ),
    inference(forward_demodulation,[],[f2888,f185])).

fof(f2888,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))) != k4_xboole_0(sK0,sK0)
    | spl5_2 ),
    inference(superposition,[],[f2884,f175])).

fof(f2884,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k4_xboole_0(sK0,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f2882])).

fof(f2882,plain,
    ( spl5_2
  <=> k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2885,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2637,f210,f2882])).

fof(f210,plain,
    ( spl5_1
  <=> k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2637,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k4_xboole_0(sK0,sK0)
    | spl5_1 ),
    inference(backward_demodulation,[],[f2497,f2611])).

fof(f2611,plain,(
    ! [X57,X58] : k3_xboole_0(X57,k4_xboole_0(X58,X58)) = k4_xboole_0(X57,X57) ),
    inference(superposition,[],[f180,f2469])).

fof(f2469,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X6)) = X5 ),
    inference(backward_demodulation,[],[f1602,f2451])).

fof(f2451,plain,(
    ! [X54,X53] : k4_xboole_0(X53,X53) = k3_xboole_0(X53,k4_xboole_0(X54,X53)) ),
    inference(superposition,[],[f180,f1649])).

fof(f1649,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f1648,f312])).

fof(f312,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f310,f311])).

fof(f311,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f307,f309])).

fof(f307,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,k4_xboole_0(X2,X3)),k3_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f178,f180])).

fof(f178,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f91])).

fof(f91,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f310,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f306,f187])).

fof(f306,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f179,f180])).

fof(f1648,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1612,f187])).

fof(f1612,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f173,f164])).

fof(f164,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f173,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f1602,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k3_xboole_0(X6,k4_xboole_0(X5,X6))) = X5 ),
    inference(forward_demodulation,[],[f1601,f312])).

fof(f1601,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k3_xboole_0(X6,k4_xboole_0(X5,X6))) = k2_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f1559,f187])).

fof(f1559,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k3_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f172,f179])).

fof(f172,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f2497,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK1))
    | spl5_1 ),
    inference(backward_demodulation,[],[f1466,f2451])).

fof(f1466,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | spl5_1 ),
    inference(forward_demodulation,[],[f1465,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1465,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(forward_demodulation,[],[f1464,f162])).

fof(f1464,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k3_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(forward_demodulation,[],[f1463,f180])).

fof(f1463,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl5_1 ),
    inference(backward_demodulation,[],[f797,f1462])).

fof(f1462,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k4_xboole_0(X7,k2_xboole_0(X6,X5))) = k3_xboole_0(X5,k4_xboole_0(X7,X5)) ),
    inference(forward_demodulation,[],[f1431,f174])).

fof(f1431,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k4_xboole_0(X7,k2_xboole_0(X6,X5))) = k4_xboole_0(k3_xboole_0(X5,X7),X5) ),
    inference(superposition,[],[f170,f236])).

fof(f236,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f161,f187])).

fof(f170,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f797,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))))
    | spl5_1 ),
    inference(backward_demodulation,[],[f508,f779])).

fof(f508,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f507,f175])).

fof(f507,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f503,f174])).

fof(f503,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) != k4_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f212,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f212,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f210])).

fof(f213,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f144,f210])).

fof(f144,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f137])).

fof(f137,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f105,f136])).

fof(f136,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f105,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f94])).

fof(f94,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f93])).

fof(f93,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).
%------------------------------------------------------------------------------
