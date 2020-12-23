%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:44 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 999 expanded)
%              Number of leaves         :   14 ( 329 expanded)
%              Depth                    :   23
%              Number of atoms          :  234 (1377 expanded)
%              Number of equality atoms :   97 ( 931 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1945,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f1688,f1710,f1714,f1943])).

fof(f1943,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f1942])).

fof(f1942,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f1941,f1716])).

fof(f1716,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl5_2 ),
    inference(resolution,[],[f1715,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1715,plain,
    ( r1_xboole_0(sK0,sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f31,f58])).

fof(f58,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f31,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1941,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_1
    | spl5_2 ),
    inference(backward_demodulation,[],[f1719,f1934])).

fof(f1934,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | ~ spl5_1 ),
    inference(superposition,[],[f46,f1908])).

fof(f1908,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1907,f75])).

fof(f75,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f72,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f72,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f69,f33])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f69,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f38,f33])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1907,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1893,f35])).

fof(f1893,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0))
    | ~ spl5_1 ),
    inference(superposition,[],[f1892,f46])).

fof(f1892,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1891,f402])).

fof(f402,plain,(
    ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,X7)) ),
    inference(backward_demodulation,[],[f167,f383])).

fof(f383,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f369,f33])).

fof(f369,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f167,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k2_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X8,X7)) ),
    inference(superposition,[],[f38,f142])).

fof(f142,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f118,f35])).

fof(f118,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f114,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f114,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f37,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f38,f35])).

fof(f1891,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1878,f46])).

fof(f1878,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | ~ spl5_1 ),
    inference(superposition,[],[f1402,f1746])).

fof(f1746,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_1 ),
    inference(superposition,[],[f1729,f35])).

fof(f1729,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1728,f75])).

fof(f1728,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1720,f35])).

fof(f1720,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl5_1 ),
    inference(superposition,[],[f37,f1702])).

fof(f1702,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f55,f51])).

fof(f55,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1402,plain,(
    ! [X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = X4 ),
    inference(backward_demodulation,[],[f68,f1400])).

fof(f1400,plain,(
    ! [X23,X22] : k4_xboole_0(X22,k4_xboole_0(X23,X22)) = X22 ),
    inference(forward_demodulation,[],[f1399,f33])).

fof(f1399,plain,(
    ! [X23,X22] : k4_xboole_0(X22,k1_xboole_0) = k4_xboole_0(X22,k4_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f1398,f403])).

fof(f403,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f152,f383])).

fof(f152,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f38,f118])).

fof(f1398,plain,(
    ! [X23,X22] : k4_xboole_0(X22,k4_xboole_0(X22,k2_xboole_0(X22,X23))) = k4_xboole_0(X22,k4_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f1358,f68])).

fof(f1358,plain,(
    ! [X23,X22] : k4_xboole_0(X22,k4_xboole_0(X22,k2_xboole_0(X22,X23))) = k4_xboole_0(k2_xboole_0(X22,X23),k4_xboole_0(X23,X22)) ),
    inference(superposition,[],[f47,f66])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f36,f36])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f68,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f38,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1719,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl5_2 ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f45,f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1714,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f1713])).

fof(f1713,plain,
    ( $false
    | spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f58,f1712])).

fof(f1712,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl5_3 ),
    inference(subsumption_resolution,[],[f31,f64])).

fof(f64,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1710,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f1709])).

fof(f1709,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f1708,f383])).

fof(f1708,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl5_2
    | spl5_3 ),
    inference(forward_demodulation,[],[f1707,f1690])).

fof(f1690,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1689,f1593])).

fof(f1593,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1592,f75])).

fof(f1592,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1578,f35])).

fof(f1578,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0))
    | ~ spl5_2 ),
    inference(superposition,[],[f1543,f46])).

fof(f1543,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1542,f402])).

fof(f1542,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK0)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1496,f46])).

fof(f1496,plain,
    ( sK0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK0))
    | ~ spl5_2 ),
    inference(superposition,[],[f1402,f916])).

fof(f916,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_2 ),
    inference(superposition,[],[f508,f35])).

fof(f508,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f507,f75])).

fof(f507,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f506,f35])).

fof(f506,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl5_2 ),
    inference(superposition,[],[f37,f382])).

fof(f382,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_2 ),
    inference(resolution,[],[f51,f59])).

fof(f59,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f1689,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1663,f35])).

fof(f1663,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f1641,f615])).

fof(f615,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(k2_xboole_0(X8,X7),X7) ),
    inference(forward_demodulation,[],[f614,f75])).

fof(f614,plain,(
    ! [X8,X7] : k2_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f584,f35])).

fof(f584,plain,(
    ! [X8,X7] : k2_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0) ),
    inference(superposition,[],[f579,f74])).

fof(f74,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f71,f37])).

fof(f71,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f37,f38])).

fof(f579,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f562,f130])).

fof(f130,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f129,f74])).

fof(f129,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f122,f35])).

fof(f122,plain,(
    ! [X6,X5] : k2_xboole_0(k2_xboole_0(X6,X5),X5) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f74,f74])).

fof(f562,plain,(
    ! [X4,X3] : k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f37,f461])).

fof(f461,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) ),
    inference(backward_demodulation,[],[f127,f402])).

fof(f127,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f38,f74])).

fof(f1641,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0))
    | ~ spl5_2 ),
    inference(superposition,[],[f46,f1593])).

fof(f1707,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl5_3 ),
    inference(resolution,[],[f64,f50])).

fof(f1688,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f1687])).

fof(f1687,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1686,f383])).

fof(f1686,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f367,f1685])).

fof(f1685,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1662,f1593])).

fof(f1662,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(superposition,[],[f1641,f153])).

fof(f153,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f151,f97])).

fof(f97,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(backward_demodulation,[],[f89,f92])).

fof(f92,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f90,f82])).

fof(f82,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f38,f75])).

fof(f90,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f88,f72])).

fof(f88,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f37,f82])).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f37,f82])).

fof(f151,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f74,f118])).

fof(f367,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(resolution,[],[f50,f54])).

fof(f54,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f65,plain,
    ( ~ spl5_2
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f26,f62,f53,f57])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f30,f57,f53])).

fof(f30,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:25:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (21917)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (21913)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (21923)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (21911)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (21926)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (21925)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (21924)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (21918)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (21915)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (21921)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (21912)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (21922)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (21922)Refutation not found, incomplete strategy% (21922)------------------------------
% 0.21/0.51  % (21922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21922)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21922)Memory used [KB]: 10618
% 0.21/0.51  % (21922)Time elapsed: 0.086 s
% 0.21/0.51  % (21922)------------------------------
% 0.21/0.51  % (21922)------------------------------
% 0.21/0.51  % (21914)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (21928)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (21927)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.53  % (21916)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.53  % (21920)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.54  % (21919)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.67/0.58  % (21925)Refutation found. Thanks to Tanya!
% 1.67/0.58  % SZS status Theorem for theBenchmark
% 1.67/0.58  % SZS output start Proof for theBenchmark
% 1.67/0.58  fof(f1945,plain,(
% 1.67/0.58    $false),
% 1.67/0.58    inference(avatar_sat_refutation,[],[f60,f65,f1688,f1710,f1714,f1943])).
% 1.67/0.58  fof(f1943,plain,(
% 1.67/0.58    ~spl5_1 | spl5_2),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f1942])).
% 1.67/0.58  fof(f1942,plain,(
% 1.67/0.58    $false | (~spl5_1 | spl5_2)),
% 1.67/0.58    inference(subsumption_resolution,[],[f1941,f1716])).
% 1.67/0.58  fof(f1716,plain,(
% 1.67/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl5_2),
% 1.67/0.58    inference(resolution,[],[f1715,f51])).
% 1.67/0.58  fof(f51,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.67/0.58    inference(definition_unfolding,[],[f44,f36])).
% 1.67/0.58  fof(f36,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f10])).
% 1.67/0.58  fof(f10,axiom,(
% 1.67/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.67/0.58  fof(f44,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f25])).
% 1.67/0.58  fof(f25,plain,(
% 1.67/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.67/0.58    inference(nnf_transformation,[],[f3])).
% 1.67/0.58  fof(f3,axiom,(
% 1.67/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.67/0.58  fof(f1715,plain,(
% 1.67/0.58    r1_xboole_0(sK0,sK2) | spl5_2),
% 1.67/0.58    inference(subsumption_resolution,[],[f31,f58])).
% 1.67/0.58  fof(f58,plain,(
% 1.67/0.58    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl5_2),
% 1.67/0.58    inference(avatar_component_clause,[],[f57])).
% 1.67/0.58  fof(f57,plain,(
% 1.67/0.58    spl5_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.67/0.58  fof(f31,plain,(
% 1.67/0.58    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f20,plain,(
% 1.67/0.58    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 1.67/0.58  fof(f19,plain,(
% 1.67/0.58    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f16,plain,(
% 1.67/0.58    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.67/0.58    inference(ennf_transformation,[],[f13])).
% 1.67/0.58  fof(f13,negated_conjecture,(
% 1.67/0.58    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.67/0.58    inference(negated_conjecture,[],[f12])).
% 1.67/0.58  fof(f12,conjecture,(
% 1.67/0.58    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.67/0.58  fof(f1941,plain,(
% 1.67/0.58    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl5_1 | spl5_2)),
% 1.67/0.58    inference(backward_demodulation,[],[f1719,f1934])).
% 1.67/0.58  fof(f1934,plain,(
% 1.67/0.58    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | ~spl5_1),
% 1.67/0.58    inference(superposition,[],[f46,f1908])).
% 1.67/0.58  fof(f1908,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_1),
% 1.67/0.58    inference(forward_demodulation,[],[f1907,f75])).
% 1.67/0.58  fof(f75,plain,(
% 1.67/0.58    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.67/0.58    inference(superposition,[],[f72,f35])).
% 1.67/0.58  fof(f35,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f1])).
% 1.67/0.58  fof(f1,axiom,(
% 1.67/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.67/0.58  fof(f72,plain,(
% 1.67/0.58    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.67/0.58    inference(forward_demodulation,[],[f69,f33])).
% 1.67/0.58  fof(f33,plain,(
% 1.67/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.67/0.58    inference(cnf_transformation,[],[f7])).
% 1.67/0.58  fof(f7,axiom,(
% 1.67/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.67/0.58  fof(f69,plain,(
% 1.67/0.58    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 1.67/0.58    inference(superposition,[],[f38,f33])).
% 1.67/0.58  fof(f38,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f8])).
% 1.67/0.58  fof(f8,axiom,(
% 1.67/0.58    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.67/0.58  fof(f1907,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)) | ~spl5_1),
% 1.67/0.58    inference(forward_demodulation,[],[f1893,f35])).
% 1.67/0.58  fof(f1893,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)) | ~spl5_1),
% 1.67/0.58    inference(superposition,[],[f1892,f46])).
% 1.67/0.58  fof(f1892,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl5_1),
% 1.67/0.58    inference(forward_demodulation,[],[f1891,f402])).
% 1.67/0.58  fof(f402,plain,(
% 1.67/0.58    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,X7))) )),
% 1.67/0.58    inference(backward_demodulation,[],[f167,f383])).
% 1.67/0.58  fof(f383,plain,(
% 1.67/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.67/0.58    inference(forward_demodulation,[],[f369,f33])).
% 1.67/0.58  fof(f369,plain,(
% 1.67/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.67/0.58    inference(resolution,[],[f51,f32])).
% 1.67/0.58  fof(f32,plain,(
% 1.67/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f11])).
% 1.67/0.58  fof(f11,axiom,(
% 1.67/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.67/0.58  fof(f167,plain,(
% 1.67/0.58    ( ! [X8,X7] : (k4_xboole_0(X7,k2_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X8,X7))) )),
% 1.67/0.58    inference(superposition,[],[f38,f142])).
% 1.67/0.58  fof(f142,plain,(
% 1.67/0.58    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 1.67/0.58    inference(superposition,[],[f118,f35])).
% 1.67/0.58  fof(f118,plain,(
% 1.67/0.58    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f114,f37])).
% 1.67/0.58  fof(f37,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f6])).
% 1.67/0.58  fof(f6,axiom,(
% 1.67/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.67/0.58  fof(f114,plain,(
% 1.67/0.58    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.67/0.58    inference(superposition,[],[f37,f66])).
% 1.67/0.58  fof(f66,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 1.67/0.58    inference(superposition,[],[f38,f35])).
% 1.67/0.58  fof(f1891,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) | ~spl5_1),
% 1.67/0.58    inference(forward_demodulation,[],[f1878,f46])).
% 1.67/0.58  fof(f1878,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | ~spl5_1),
% 1.67/0.58    inference(superposition,[],[f1402,f1746])).
% 1.67/0.58  fof(f1746,plain,(
% 1.67/0.58    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_1),
% 1.67/0.58    inference(superposition,[],[f1729,f35])).
% 1.67/0.58  fof(f1729,plain,(
% 1.67/0.58    k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl5_1),
% 1.67/0.58    inference(forward_demodulation,[],[f1728,f75])).
% 1.67/0.58  fof(f1728,plain,(
% 1.67/0.58    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl5_1),
% 1.67/0.58    inference(forward_demodulation,[],[f1720,f35])).
% 1.67/0.58  fof(f1720,plain,(
% 1.67/0.58    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl5_1),
% 1.67/0.58    inference(superposition,[],[f37,f1702])).
% 1.67/0.58  fof(f1702,plain,(
% 1.67/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_1),
% 1.67/0.58    inference(resolution,[],[f55,f51])).
% 1.67/0.58  fof(f55,plain,(
% 1.67/0.58    r1_xboole_0(sK0,sK1) | ~spl5_1),
% 1.67/0.58    inference(avatar_component_clause,[],[f53])).
% 1.67/0.58  fof(f53,plain,(
% 1.67/0.58    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.67/0.58  fof(f1402,plain,(
% 1.67/0.58    ( ! [X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) = X4) )),
% 1.67/0.58    inference(backward_demodulation,[],[f68,f1400])).
% 1.67/0.58  fof(f1400,plain,(
% 1.67/0.58    ( ! [X23,X22] : (k4_xboole_0(X22,k4_xboole_0(X23,X22)) = X22) )),
% 1.67/0.58    inference(forward_demodulation,[],[f1399,f33])).
% 1.67/0.58  fof(f1399,plain,(
% 1.67/0.58    ( ! [X23,X22] : (k4_xboole_0(X22,k1_xboole_0) = k4_xboole_0(X22,k4_xboole_0(X23,X22))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f1398,f403])).
% 1.67/0.58  fof(f403,plain,(
% 1.67/0.58    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 1.67/0.58    inference(backward_demodulation,[],[f152,f383])).
% 1.67/0.58  fof(f152,plain,(
% 1.67/0.58    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 1.67/0.58    inference(superposition,[],[f38,f118])).
% 1.67/0.58  fof(f1398,plain,(
% 1.67/0.58    ( ! [X23,X22] : (k4_xboole_0(X22,k4_xboole_0(X22,k2_xboole_0(X22,X23))) = k4_xboole_0(X22,k4_xboole_0(X23,X22))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f1358,f68])).
% 1.67/0.58  fof(f1358,plain,(
% 1.67/0.58    ( ! [X23,X22] : (k4_xboole_0(X22,k4_xboole_0(X22,k2_xboole_0(X22,X23))) = k4_xboole_0(k2_xboole_0(X22,X23),k4_xboole_0(X23,X22))) )),
% 1.67/0.58    inference(superposition,[],[f47,f66])).
% 1.67/0.58  fof(f47,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.67/0.58    inference(definition_unfolding,[],[f34,f36,f36])).
% 1.67/0.58  fof(f34,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f2])).
% 1.67/0.58  fof(f2,axiom,(
% 1.67/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.67/0.58  fof(f68,plain,(
% 1.67/0.58    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) )),
% 1.67/0.58    inference(superposition,[],[f38,f37])).
% 1.67/0.58  fof(f46,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f9])).
% 1.67/0.58  fof(f9,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.67/0.58  fof(f1719,plain,(
% 1.67/0.58    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl5_2),
% 1.67/0.58    inference(resolution,[],[f58,f50])).
% 1.67/0.58  fof(f50,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.67/0.58    inference(definition_unfolding,[],[f45,f36])).
% 1.67/0.58  fof(f45,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.67/0.58    inference(cnf_transformation,[],[f25])).
% 1.67/0.58  fof(f1714,plain,(
% 1.67/0.58    spl5_2 | spl5_3),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f1713])).
% 1.67/0.58  fof(f1713,plain,(
% 1.67/0.58    $false | (spl5_2 | spl5_3)),
% 1.67/0.58    inference(subsumption_resolution,[],[f58,f1712])).
% 1.67/0.58  fof(f1712,plain,(
% 1.67/0.58    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl5_3),
% 1.67/0.58    inference(subsumption_resolution,[],[f31,f64])).
% 1.67/0.58  fof(f64,plain,(
% 1.67/0.58    ~r1_xboole_0(sK0,sK2) | spl5_3),
% 1.67/0.58    inference(avatar_component_clause,[],[f62])).
% 1.67/0.58  fof(f62,plain,(
% 1.67/0.58    spl5_3 <=> r1_xboole_0(sK0,sK2)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.67/0.58  fof(f1710,plain,(
% 1.67/0.58    ~spl5_2 | spl5_3),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f1709])).
% 1.67/0.58  fof(f1709,plain,(
% 1.67/0.58    $false | (~spl5_2 | spl5_3)),
% 1.67/0.58    inference(subsumption_resolution,[],[f1708,f383])).
% 1.67/0.58  fof(f1708,plain,(
% 1.67/0.58    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl5_2 | spl5_3)),
% 1.67/0.58    inference(forward_demodulation,[],[f1707,f1690])).
% 1.67/0.58  fof(f1690,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(sK0,sK2) | ~spl5_2),
% 1.67/0.58    inference(forward_demodulation,[],[f1689,f1593])).
% 1.67/0.58  fof(f1593,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_2),
% 1.67/0.58    inference(forward_demodulation,[],[f1592,f75])).
% 1.67/0.58  fof(f1592,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) | ~spl5_2),
% 1.67/0.58    inference(forward_demodulation,[],[f1578,f35])).
% 1.67/0.58  fof(f1578,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),k1_xboole_0)) | ~spl5_2),
% 1.67/0.58    inference(superposition,[],[f1543,f46])).
% 1.67/0.58  fof(f1543,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) | ~spl5_2),
% 1.67/0.58    inference(forward_demodulation,[],[f1542,f402])).
% 1.67/0.58  fof(f1542,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK0))) | ~spl5_2),
% 1.67/0.58    inference(forward_demodulation,[],[f1496,f46])).
% 1.67/0.58  fof(f1496,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK0)) | ~spl5_2),
% 1.67/0.58    inference(superposition,[],[f1402,f916])).
% 1.67/0.58  fof(f916,plain,(
% 1.67/0.58    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl5_2),
% 1.67/0.58    inference(superposition,[],[f508,f35])).
% 1.67/0.58  fof(f508,plain,(
% 1.67/0.58    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK0) | ~spl5_2),
% 1.67/0.58    inference(forward_demodulation,[],[f507,f75])).
% 1.67/0.58  fof(f507,plain,(
% 1.67/0.58    k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl5_2),
% 1.67/0.58    inference(forward_demodulation,[],[f506,f35])).
% 1.67/0.58  fof(f506,plain,(
% 1.67/0.58    k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) | ~spl5_2),
% 1.67/0.58    inference(superposition,[],[f37,f382])).
% 1.67/0.58  fof(f382,plain,(
% 1.67/0.58    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl5_2),
% 1.67/0.58    inference(resolution,[],[f51,f59])).
% 1.67/0.58  fof(f59,plain,(
% 1.67/0.58    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_2),
% 1.67/0.58    inference(avatar_component_clause,[],[f57])).
% 1.67/0.58  fof(f1689,plain,(
% 1.67/0.58    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK2) | ~spl5_2),
% 1.67/0.58    inference(forward_demodulation,[],[f1663,f35])).
% 1.67/0.58  fof(f1663,plain,(
% 1.67/0.58    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) | ~spl5_2),
% 1.67/0.58    inference(superposition,[],[f1641,f615])).
% 1.67/0.58  fof(f615,plain,(
% 1.67/0.58    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(k2_xboole_0(X8,X7),X7)) )),
% 1.67/0.58    inference(forward_demodulation,[],[f614,f75])).
% 1.67/0.58  fof(f614,plain,(
% 1.67/0.58    ( ! [X8,X7] : (k2_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X7,X8))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f584,f35])).
% 1.67/0.58  fof(f584,plain,(
% 1.67/0.58    ( ! [X8,X7] : (k2_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0)) )),
% 1.67/0.58    inference(superposition,[],[f579,f74])).
% 1.67/0.58  fof(f74,plain,(
% 1.67/0.58    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f71,f37])).
% 1.67/0.58  fof(f71,plain,(
% 1.67/0.58    ( ! [X2,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 1.67/0.58    inference(superposition,[],[f37,f38])).
% 1.67/0.58  fof(f579,plain,(
% 1.67/0.58    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0)) )),
% 1.67/0.58    inference(forward_demodulation,[],[f562,f130])).
% 1.67/0.58  fof(f130,plain,(
% 1.67/0.58    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f129,f74])).
% 1.67/0.58  fof(f129,plain,(
% 1.67/0.58    ( ! [X6,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X5)) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 1.67/0.58    inference(forward_demodulation,[],[f122,f35])).
% 1.67/0.58  fof(f122,plain,(
% 1.67/0.58    ( ! [X6,X5] : (k2_xboole_0(k2_xboole_0(X6,X5),X5) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))) )),
% 1.67/0.58    inference(superposition,[],[f74,f74])).
% 1.67/0.58  fof(f562,plain,(
% 1.67/0.58    ( ! [X4,X3] : (k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4))) )),
% 1.67/0.58    inference(superposition,[],[f37,f461])).
% 1.67/0.58  fof(f461,plain,(
% 1.67/0.58    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))) )),
% 1.67/0.58    inference(backward_demodulation,[],[f127,f402])).
% 1.67/0.58  fof(f127,plain,(
% 1.67/0.58    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))) )),
% 1.67/0.58    inference(superposition,[],[f38,f74])).
% 1.67/0.58  fof(f1641,plain,(
% 1.67/0.58    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0))) ) | ~spl5_2),
% 1.67/0.58    inference(superposition,[],[f46,f1593])).
% 1.67/0.58  fof(f1707,plain,(
% 1.67/0.58    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl5_3),
% 1.67/0.58    inference(resolution,[],[f64,f50])).
% 1.67/0.58  fof(f1688,plain,(
% 1.67/0.58    spl5_1 | ~spl5_2),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f1687])).
% 1.67/0.58  fof(f1687,plain,(
% 1.67/0.58    $false | (spl5_1 | ~spl5_2)),
% 1.67/0.58    inference(subsumption_resolution,[],[f1686,f383])).
% 1.67/0.58  fof(f1686,plain,(
% 1.67/0.58    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl5_1 | ~spl5_2)),
% 1.67/0.58    inference(backward_demodulation,[],[f367,f1685])).
% 1.67/0.58  fof(f1685,plain,(
% 1.67/0.58    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_2),
% 1.67/0.58    inference(forward_demodulation,[],[f1662,f1593])).
% 1.67/0.58  fof(f1662,plain,(
% 1.67/0.58    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK1) | ~spl5_2),
% 1.67/0.58    inference(superposition,[],[f1641,f153])).
% 1.67/0.58  fof(f153,plain,(
% 1.67/0.58    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 1.67/0.58    inference(forward_demodulation,[],[f151,f97])).
% 1.67/0.58  fof(f97,plain,(
% 1.67/0.58    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.67/0.58    inference(backward_demodulation,[],[f89,f92])).
% 1.67/0.58  fof(f92,plain,(
% 1.67/0.58    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.67/0.58    inference(superposition,[],[f90,f82])).
% 1.67/0.58  fof(f82,plain,(
% 1.67/0.58    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 1.67/0.58    inference(superposition,[],[f38,f75])).
% 1.67/0.58  fof(f90,plain,(
% 1.67/0.58    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.67/0.58    inference(forward_demodulation,[],[f88,f72])).
% 1.67/0.58  fof(f88,plain,(
% 1.67/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 1.67/0.58    inference(superposition,[],[f37,f82])).
% 1.67/0.58  fof(f89,plain,(
% 1.67/0.58    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(X0,X0)) )),
% 1.67/0.58    inference(superposition,[],[f37,f82])).
% 1.67/0.58  fof(f151,plain,(
% 1.67/0.58    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))) )),
% 1.67/0.58    inference(superposition,[],[f74,f118])).
% 1.67/0.58  fof(f367,plain,(
% 1.67/0.58    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl5_1),
% 1.67/0.58    inference(resolution,[],[f50,f54])).
% 1.67/0.58  fof(f54,plain,(
% 1.67/0.58    ~r1_xboole_0(sK0,sK1) | spl5_1),
% 1.67/0.58    inference(avatar_component_clause,[],[f53])).
% 1.67/0.58  fof(f65,plain,(
% 1.67/0.58    ~spl5_2 | ~spl5_1 | ~spl5_3),
% 1.67/0.58    inference(avatar_split_clause,[],[f26,f62,f53,f57])).
% 1.67/0.58  fof(f26,plain,(
% 1.67/0.58    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  fof(f60,plain,(
% 1.67/0.58    spl5_1 | spl5_2),
% 1.67/0.58    inference(avatar_split_clause,[],[f30,f57,f53])).
% 1.67/0.58  fof(f30,plain,(
% 1.67/0.58    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 1.67/0.58    inference(cnf_transformation,[],[f20])).
% 1.67/0.58  % SZS output end Proof for theBenchmark
% 1.67/0.58  % (21925)------------------------------
% 1.67/0.58  % (21925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (21925)Termination reason: Refutation
% 1.67/0.58  
% 1.67/0.58  % (21925)Memory used [KB]: 7291
% 1.67/0.58  % (21925)Time elapsed: 0.155 s
% 1.67/0.58  % (21925)------------------------------
% 1.67/0.58  % (21925)------------------------------
% 1.67/0.59  % (21910)Success in time 0.228 s
%------------------------------------------------------------------------------
