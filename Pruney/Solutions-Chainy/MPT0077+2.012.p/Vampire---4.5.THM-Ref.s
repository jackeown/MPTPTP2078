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
% DateTime   : Thu Dec  3 12:30:45 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   84 (1046 expanded)
%              Number of leaves         :   11 ( 321 expanded)
%              Depth                    :   23
%              Number of atoms          :  170 (2153 expanded)
%              Number of equality atoms :   71 ( 913 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1511,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1509,f1418])).

fof(f1418,plain,(
    sP0(sK3,sK1,sK2) ),
    inference(subsumption_resolution,[],[f1381,f1396])).

fof(f1396,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f959,f1358])).

fof(f1358,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f1348,f1311])).

fof(f1311,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f1309,f521])).

fof(f521,plain,
    ( ~ sP0(sK3,sK1,sK2)
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f519,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X0)
        & r1_xboole_0(X1,X2)
        & ~ r1_xboole_0(X1,k2_xboole_0(X2,X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) )
      | ~ sP0(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) )
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f519,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f517,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f34,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f517,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f36,f505])).

fof(f505,plain,
    ( sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f498,f26])).

fof(f498,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f35,f240])).

fof(f240,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f220,f26])).

fof(f220,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f35,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f57,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f57,plain,
    ( r1_xboole_0(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(resolution,[],[f53,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,
    ( sP0(sK3,sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(resolution,[],[f37,f24])).

fof(f24,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sP0(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
      & ( ~ r1_xboole_0(sK1,sK3)
        | ~ r1_xboole_0(sK1,sK2) ) )
    | sP0(sK3,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | sP0(X2,X0,X1) )
   => ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
        & ( ~ r1_xboole_0(sK1,sK3)
          | ~ r1_xboole_0(sK1,sK2) ) )
      | sP0(sK3,sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | sP0(X2,X0,X1) ) ),
    inference(definition_folding,[],[f12,f13])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1309,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK2)
    | sP0(sK3,sK1,sK2) ),
    inference(resolution,[],[f1298,f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_xboole_0(sK1,sK2)
    | sP0(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f1298,plain,
    ( r1_xboole_0(sK1,sK3)
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f1064,f505])).

fof(f1064,plain,(
    ! [X52,X53,X51] : r1_xboole_0(k4_xboole_0(X51,k2_xboole_0(X52,X53)),X53) ),
    inference(superposition,[],[f959,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1348,plain,
    ( r1_xboole_0(sK1,sK2)
    | sK1 = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f1270,f505])).

fof(f1270,plain,(
    ! [X4,X2,X3] : r1_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X2)),X3) ),
    inference(superposition,[],[f1064,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f959,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(subsumption_resolution,[],[f905,f81])).

fof(f81,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f33,f38])).

fof(f905,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0)))
      | r1_xboole_0(k4_xboole_0(X1,X0),X0) ) ),
    inference(superposition,[],[f88,f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f88,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4))))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(forward_demodulation,[],[f83,f33])).

fof(f83,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(superposition,[],[f36,f33])).

fof(f1381,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | sP0(sK3,sK1,sK2) ),
    inference(resolution,[],[f1371,f23])).

fof(f1371,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f959,f1357])).

fof(f1357,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f1347,f1308])).

fof(f1308,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | sK1 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f1306,f554])).

fof(f554,plain,
    ( ~ sP0(sK3,sK1,sK2)
    | sK1 = k4_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f552,f20])).

fof(f552,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sK1 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f550,f38])).

fof(f550,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f36,f531])).

fof(f531,plain,
    ( sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f524,f26])).

fof(f524,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)
    | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f35,f241])).

fof(f241,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f221,f26])).

fof(f221,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f35,f59])).

fof(f59,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f56,f37])).

fof(f56,plain,
    ( r1_xboole_0(sK1,sK3)
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(resolution,[],[f53,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1306,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ r1_xboole_0(sK1,sK2)
    | sP0(sK3,sK1,sK2) ),
    inference(resolution,[],[f1297,f23])).

fof(f1297,plain,
    ( r1_xboole_0(sK1,sK3)
    | sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f1064,f531])).

fof(f1347,plain,
    ( r1_xboole_0(sK1,sK2)
    | sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f1270,f531])).

fof(f1509,plain,(
    ~ sP0(sK3,sK1,sK2) ),
    inference(resolution,[],[f1506,f20])).

fof(f1506,plain,(
    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f1483,f28])).

fof(f1483,plain,(
    r1_xboole_0(sK1,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[],[f1442,f1358])).

fof(f1442,plain,(
    ! [X13] : r1_xboole_0(k4_xboole_0(sK1,X13),k2_xboole_0(sK3,X13)) ),
    inference(superposition,[],[f959,f1366])).

fof(f1366,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f33,f1357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:47:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (31554)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (31544)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (31545)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (31546)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (31551)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (31548)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (31543)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (31555)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (31553)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (31542)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (31547)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (31541)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (31558)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (31552)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (31556)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (31550)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (31549)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (31557)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.37/0.54  % (31553)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f1511,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(subsumption_resolution,[],[f1509,f1418])).
% 1.37/0.54  fof(f1418,plain,(
% 1.37/0.54    sP0(sK3,sK1,sK2)),
% 1.37/0.54    inference(subsumption_resolution,[],[f1381,f1396])).
% 1.37/0.54  fof(f1396,plain,(
% 1.37/0.54    r1_xboole_0(sK1,sK2)),
% 1.37/0.54    inference(superposition,[],[f959,f1358])).
% 1.37/0.54  fof(f1358,plain,(
% 1.37/0.54    sK1 = k4_xboole_0(sK1,sK2)),
% 1.37/0.54    inference(subsumption_resolution,[],[f1348,f1311])).
% 1.37/0.54  fof(f1311,plain,(
% 1.37/0.54    ~r1_xboole_0(sK1,sK2) | sK1 = k4_xboole_0(sK1,sK2)),
% 1.37/0.54    inference(subsumption_resolution,[],[f1309,f521])).
% 1.37/0.54  fof(f521,plain,(
% 1.37/0.54    ~sP0(sK3,sK1,sK2) | sK1 = k4_xboole_0(sK1,sK2)),
% 1.37/0.54    inference(resolution,[],[f519,f20])).
% 1.37/0.54  fof(f20,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k2_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f16,plain,(
% 1.37/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X1,X0) & r1_xboole_0(X1,X2) & ~r1_xboole_0(X1,k2_xboole_0(X2,X0))) | ~sP0(X0,X1,X2))),
% 1.37/0.54    inference(rectify,[],[f15])).
% 1.37/0.54  fof(f15,plain,(
% 1.37/0.54    ! [X2,X0,X1] : ((r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) | ~sP0(X2,X0,X1))),
% 1.37/0.54    inference(nnf_transformation,[],[f13])).
% 1.37/0.54  fof(f13,plain,(
% 1.37/0.54    ! [X2,X0,X1] : ((r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) | ~sP0(X2,X0,X1))),
% 1.37/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.37/0.54  fof(f519,plain,(
% 1.37/0.54    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sK1 = k4_xboole_0(sK1,sK2)),
% 1.37/0.54    inference(subsumption_resolution,[],[f517,f38])).
% 1.37/0.54  fof(f38,plain,(
% 1.37/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.37/0.54    inference(forward_demodulation,[],[f34,f26])).
% 1.37/0.54  fof(f26,plain,(
% 1.37/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.37/0.54    inference(cnf_transformation,[],[f5])).
% 1.37/0.54  fof(f5,axiom,(
% 1.37/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f25,f29])).
% 1.37/0.54  fof(f29,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f8])).
% 1.37/0.54  fof(f8,axiom,(
% 1.37/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.37/0.54  fof(f25,plain,(
% 1.37/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.37/0.54  fof(f517,plain,(
% 1.37/0.54    k1_xboole_0 != k4_xboole_0(sK1,sK1) | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sK1 = k4_xboole_0(sK1,sK2)),
% 1.37/0.54    inference(superposition,[],[f36,f505])).
% 1.37/0.54  fof(f505,plain,(
% 1.37/0.54    sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sK1 = k4_xboole_0(sK1,sK2)),
% 1.37/0.54    inference(forward_demodulation,[],[f498,f26])).
% 1.37/0.54  fof(f498,plain,(
% 1.37/0.54    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 1.37/0.54    inference(superposition,[],[f35,f240])).
% 1.37/0.54  fof(f240,plain,(
% 1.37/0.54    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 1.37/0.54    inference(forward_demodulation,[],[f220,f26])).
% 1.37/0.54  fof(f220,plain,(
% 1.37/0.54    k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.37/0.54    inference(superposition,[],[f35,f60])).
% 1.37/0.54  fof(f60,plain,(
% 1.37/0.54    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.37/0.54    inference(resolution,[],[f57,f37])).
% 1.37/0.54  fof(f37,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f31,f29])).
% 1.37/0.54  fof(f31,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f19])).
% 1.37/0.54  fof(f19,plain,(
% 1.37/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.37/0.54    inference(nnf_transformation,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.37/0.54  fof(f57,plain,(
% 1.37/0.54    r1_xboole_0(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 1.37/0.54    inference(resolution,[],[f53,f21])).
% 1.37/0.54  fof(f21,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_xboole_0(X1,X2)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f53,plain,(
% 1.37/0.54    sP0(sK3,sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 1.37/0.54    inference(resolution,[],[f37,f24])).
% 1.37/0.54  fof(f24,plain,(
% 1.37/0.54    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sP0(sK3,sK1,sK2)),
% 1.37/0.54    inference(cnf_transformation,[],[f18])).
% 1.37/0.54  fof(f18,plain,(
% 1.37/0.54    (r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | sP0(sK3,sK1,sK2)),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17])).
% 1.37/0.54  fof(f17,plain,(
% 1.37/0.54    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | sP0(X2,X0,X1)) => ((r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | sP0(sK3,sK1,sK2))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f14,plain,(
% 1.37/0.54    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | sP0(X2,X0,X1))),
% 1.37/0.54    inference(definition_folding,[],[f12,f13])).
% 1.37/0.54  fof(f12,plain,(
% 1.37/0.54    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.37/0.54    inference(ennf_transformation,[],[f10])).
% 1.37/0.54  fof(f10,negated_conjecture,(
% 1.37/0.54    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.37/0.54    inference(negated_conjecture,[],[f9])).
% 1.37/0.54  fof(f9,conjecture,(
% 1.37/0.54    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f30,f29])).
% 1.37/0.54  fof(f30,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.37/0.54  fof(f36,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f32,f29])).
% 1.37/0.54  fof(f32,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.37/0.54    inference(cnf_transformation,[],[f19])).
% 1.37/0.54  fof(f1309,plain,(
% 1.37/0.54    sK1 = k4_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK2) | sP0(sK3,sK1,sK2)),
% 1.37/0.54    inference(resolution,[],[f1298,f23])).
% 1.37/0.54  fof(f23,plain,(
% 1.37/0.54    ~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2) | sP0(sK3,sK1,sK2)),
% 1.37/0.54    inference(cnf_transformation,[],[f18])).
% 1.37/0.54  fof(f1298,plain,(
% 1.37/0.54    r1_xboole_0(sK1,sK3) | sK1 = k4_xboole_0(sK1,sK2)),
% 1.37/0.54    inference(superposition,[],[f1064,f505])).
% 1.37/0.54  fof(f1064,plain,(
% 1.37/0.54    ( ! [X52,X53,X51] : (r1_xboole_0(k4_xboole_0(X51,k2_xboole_0(X52,X53)),X53)) )),
% 1.37/0.54    inference(superposition,[],[f959,f33])).
% 1.37/0.54  fof(f33,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f6])).
% 1.37/0.54  fof(f6,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.37/0.54  fof(f1348,plain,(
% 1.37/0.54    r1_xboole_0(sK1,sK2) | sK1 = k4_xboole_0(sK1,sK2)),
% 1.37/0.54    inference(superposition,[],[f1270,f505])).
% 1.37/0.54  fof(f1270,plain,(
% 1.37/0.54    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X2)),X3)) )),
% 1.37/0.54    inference(superposition,[],[f1064,f28])).
% 1.37/0.54  fof(f28,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f1])).
% 1.37/0.54  fof(f1,axiom,(
% 1.37/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.37/0.54  fof(f959,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 1.37/0.54    inference(subsumption_resolution,[],[f905,f81])).
% 1.37/0.54  fof(f81,plain,(
% 1.37/0.54    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 1.37/0.54    inference(superposition,[],[f33,f38])).
% 1.37/0.54  fof(f905,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) | r1_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 1.37/0.54    inference(superposition,[],[f88,f27])).
% 1.37/0.54  fof(f27,plain,(
% 1.37/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.37/0.54    inference(cnf_transformation,[],[f11])).
% 1.37/0.54  fof(f11,plain,(
% 1.37/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.37/0.54    inference(rectify,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.37/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.37/0.54  fof(f88,plain,(
% 1.37/0.54    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 1.37/0.54    inference(forward_demodulation,[],[f83,f33])).
% 1.37/0.54  fof(f83,plain,(
% 1.37/0.54    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 1.37/0.54    inference(superposition,[],[f36,f33])).
% 1.37/0.54  fof(f1381,plain,(
% 1.37/0.54    ~r1_xboole_0(sK1,sK2) | sP0(sK3,sK1,sK2)),
% 1.37/0.54    inference(resolution,[],[f1371,f23])).
% 1.37/0.54  fof(f1371,plain,(
% 1.37/0.54    r1_xboole_0(sK1,sK3)),
% 1.37/0.54    inference(superposition,[],[f959,f1357])).
% 1.37/0.54  fof(f1357,plain,(
% 1.37/0.54    sK1 = k4_xboole_0(sK1,sK3)),
% 1.37/0.54    inference(subsumption_resolution,[],[f1347,f1308])).
% 1.37/0.54  fof(f1308,plain,(
% 1.37/0.54    ~r1_xboole_0(sK1,sK2) | sK1 = k4_xboole_0(sK1,sK3)),
% 1.37/0.54    inference(subsumption_resolution,[],[f1306,f554])).
% 1.37/0.54  fof(f554,plain,(
% 1.37/0.54    ~sP0(sK3,sK1,sK2) | sK1 = k4_xboole_0(sK1,sK3)),
% 1.37/0.54    inference(resolution,[],[f552,f20])).
% 1.37/0.54  fof(f552,plain,(
% 1.37/0.54    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sK1 = k4_xboole_0(sK1,sK3)),
% 1.37/0.54    inference(subsumption_resolution,[],[f550,f38])).
% 1.37/0.54  fof(f550,plain,(
% 1.37/0.54    k1_xboole_0 != k4_xboole_0(sK1,sK1) | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sK1 = k4_xboole_0(sK1,sK3)),
% 1.37/0.54    inference(superposition,[],[f36,f531])).
% 1.37/0.54  fof(f531,plain,(
% 1.37/0.54    sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | sK1 = k4_xboole_0(sK1,sK3)),
% 1.37/0.54    inference(forward_demodulation,[],[f524,f26])).
% 1.37/0.54  fof(f524,plain,(
% 1.37/0.54    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 1.37/0.54    inference(superposition,[],[f35,f241])).
% 1.37/0.54  fof(f241,plain,(
% 1.37/0.54    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | sK1 = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 1.37/0.54    inference(forward_demodulation,[],[f221,f26])).
% 1.37/0.54  fof(f221,plain,(
% 1.37/0.54    k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.37/0.54    inference(superposition,[],[f35,f59])).
% 1.37/0.54  fof(f59,plain,(
% 1.37/0.54    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.37/0.54    inference(resolution,[],[f56,f37])).
% 1.37/0.54  fof(f56,plain,(
% 1.37/0.54    r1_xboole_0(sK1,sK3) | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 1.37/0.54    inference(resolution,[],[f53,f22])).
% 1.37/0.54  fof(f22,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_xboole_0(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f1306,plain,(
% 1.37/0.54    sK1 = k4_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2) | sP0(sK3,sK1,sK2)),
% 1.37/0.54    inference(resolution,[],[f1297,f23])).
% 1.37/0.54  fof(f1297,plain,(
% 1.37/0.54    r1_xboole_0(sK1,sK3) | sK1 = k4_xboole_0(sK1,sK3)),
% 1.37/0.54    inference(superposition,[],[f1064,f531])).
% 1.37/0.54  fof(f1347,plain,(
% 1.37/0.54    r1_xboole_0(sK1,sK2) | sK1 = k4_xboole_0(sK1,sK3)),
% 1.37/0.54    inference(superposition,[],[f1270,f531])).
% 1.37/0.54  fof(f1509,plain,(
% 1.37/0.54    ~sP0(sK3,sK1,sK2)),
% 1.37/0.54    inference(resolution,[],[f1506,f20])).
% 1.37/0.54  fof(f1506,plain,(
% 1.37/0.54    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 1.37/0.54    inference(forward_demodulation,[],[f1483,f28])).
% 1.37/0.54  fof(f1483,plain,(
% 1.37/0.54    r1_xboole_0(sK1,k2_xboole_0(sK3,sK2))),
% 1.37/0.54    inference(superposition,[],[f1442,f1358])).
% 1.37/0.54  fof(f1442,plain,(
% 1.37/0.54    ( ! [X13] : (r1_xboole_0(k4_xboole_0(sK1,X13),k2_xboole_0(sK3,X13))) )),
% 1.37/0.54    inference(superposition,[],[f959,f1366])).
% 1.37/0.54  fof(f1366,plain,(
% 1.37/0.54    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0))) )),
% 1.37/0.54    inference(superposition,[],[f33,f1357])).
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (31553)------------------------------
% 1.37/0.54  % (31553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (31553)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (31553)Memory used [KB]: 2558
% 1.37/0.54  % (31553)Time elapsed: 0.123 s
% 1.37/0.54  % (31553)------------------------------
% 1.37/0.54  % (31553)------------------------------
% 1.37/0.54  % (31540)Success in time 0.178 s
%------------------------------------------------------------------------------
