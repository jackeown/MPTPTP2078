%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:31 EST 2020

% Result     : Theorem 2.51s
% Output     : Refutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 589 expanded)
%              Number of leaves         :   12 ( 198 expanded)
%              Depth                    :   36
%              Number of atoms          :   99 ( 628 expanded)
%              Number of equality atoms :   77 ( 573 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6809,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f6808])).

fof(f6808,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f6776,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f32,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f6776,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f335,f6761])).

fof(f6761,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f1344,f6716])).

fof(f6716,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f6684,f21])).

fof(f6684,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f33,f6598])).

fof(f6598,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(superposition,[],[f2346,f3581])).

fof(f3581,plain,(
    ! [X8,X7] : k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) = X7 ),
    inference(forward_demodulation,[],[f56,f1344])).

fof(f56,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) ),
    inference(superposition,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f2346,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),X0))) ),
    inference(forward_demodulation,[],[f2345,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f76,f39])).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f26,f68])).

fof(f68,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f64,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f64,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f58,f21])).

fof(f58,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f26,f21])).

fof(f2345,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),X0))) ),
    inference(forward_demodulation,[],[f2331,f39])).

fof(f2331,plain,(
    ! [X0] : k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK2)),X0) ),
    inference(superposition,[],[f37,f2029])).

fof(f2029,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f94,f2014])).

fof(f2014,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f1988,f22])).

fof(f1988,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f1973,f23])).

fof(f1973,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f1940,f1927])).

fof(f1927,plain,(
    ! [X4] : k4_xboole_0(sK0,X4) = k4_xboole_0(sK0,k4_xboole_0(X4,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f1895,f33])).

fof(f1895,plain,(
    ! [X4] : k4_xboole_0(sK0,k4_xboole_0(X4,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X4))) ),
    inference(superposition,[],[f33,f1533])).

fof(f1533,plain,(
    ! [X1] : k4_xboole_0(sK0,k4_xboole_0(sK0,X1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[],[f1521,f37])).

fof(f1521,plain,(
    ! [X19] : k4_xboole_0(sK0,X19) = k4_xboole_0(k4_xboole_0(sK0,X19),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f1344,f1486])).

fof(f1486,plain,(
    ! [X4] : k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X4)) ),
    inference(forward_demodulation,[],[f1458,f21])).

fof(f1458,plain,(
    ! [X4] : k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X4)) ),
    inference(superposition,[],[f33,f1413])).

fof(f1413,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X1))) ),
    inference(forward_demodulation,[],[f1412,f81])).

fof(f1412,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X1))) ),
    inference(forward_demodulation,[],[f1400,f39])).

fof(f1400,plain,(
    ! [X1] : k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),X1) ),
    inference(superposition,[],[f37,f1370])).

fof(f1370,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[],[f1344,f418])).

fof(f418,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f400,f21])).

fof(f400,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f33,f336])).

fof(f336,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f36,f18])).

fof(f18,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1940,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f1927,f26])).

fof(f94,plain,(
    ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k4_xboole_0(X7,X6),X6) ),
    inference(forward_demodulation,[],[f89,f53])).

fof(f53,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3) ),
    inference(superposition,[],[f26,f22])).

fof(f89,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k2_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f53,f23])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f24,f24])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1344,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f1313,f21])).

fof(f1313,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k1_xboole_0) = k4_xboole_0(X8,k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f33,f1026])).

fof(f1026,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,X9))) ),
    inference(superposition,[],[f37,f457])).

fof(f457,plain,(
    ! [X19,X18] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X18,X19),X18) ),
    inference(superposition,[],[f133,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f133,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f131,f22])).

fof(f131,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f129,f39])).

fof(f129,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f26,f96])).

fof(f96,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f91,f23])).

fof(f91,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f23,f53])).

fof(f335,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f35,f19])).

fof(f19,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:09:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (16679)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (16676)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (16674)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (16689)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (16680)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (16686)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (16683)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (16675)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (16684)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (16678)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (16681)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.53  % (16677)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.55/0.56  % (16687)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.55/0.56  % (16691)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.55/0.56  % (16690)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.55/0.56  % (16682)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.55/0.57  % (16692)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.55/0.57  % (16688)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 2.51/0.70  % (16676)Refutation found. Thanks to Tanya!
% 2.51/0.70  % SZS status Theorem for theBenchmark
% 2.51/0.70  % SZS output start Proof for theBenchmark
% 2.51/0.70  fof(f6809,plain,(
% 2.51/0.70    $false),
% 2.51/0.70    inference(trivial_inequality_removal,[],[f6808])).
% 2.51/0.70  fof(f6808,plain,(
% 2.51/0.70    k1_xboole_0 != k1_xboole_0),
% 2.51/0.70    inference(superposition,[],[f6776,f39])).
% 2.51/0.70  fof(f39,plain,(
% 2.51/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.51/0.70    inference(forward_demodulation,[],[f32,f21])).
% 2.51/0.70  fof(f21,plain,(
% 2.51/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.51/0.70    inference(cnf_transformation,[],[f5])).
% 2.51/0.70  fof(f5,axiom,(
% 2.51/0.70    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.51/0.70  fof(f32,plain,(
% 2.51/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.51/0.70    inference(definition_unfolding,[],[f20,f24])).
% 2.51/0.70  fof(f24,plain,(
% 2.51/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.51/0.70    inference(cnf_transformation,[],[f8])).
% 2.51/0.70  fof(f8,axiom,(
% 2.51/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.51/0.70  fof(f20,plain,(
% 2.51/0.70    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.51/0.70    inference(cnf_transformation,[],[f3])).
% 2.51/0.70  fof(f3,axiom,(
% 2.51/0.70    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.51/0.70  fof(f6776,plain,(
% 2.51/0.70    k1_xboole_0 != k4_xboole_0(sK1,sK1)),
% 2.51/0.70    inference(backward_demodulation,[],[f335,f6761])).
% 2.51/0.70  fof(f6761,plain,(
% 2.51/0.70    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.51/0.70    inference(superposition,[],[f1344,f6716])).
% 2.51/0.70  fof(f6716,plain,(
% 2.51/0.70    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 2.51/0.70    inference(forward_demodulation,[],[f6684,f21])).
% 2.51/0.70  fof(f6684,plain,(
% 2.51/0.70    k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 2.51/0.70    inference(superposition,[],[f33,f6598])).
% 2.51/0.70  fof(f6598,plain,(
% 2.51/0.70    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))),
% 2.51/0.70    inference(superposition,[],[f2346,f3581])).
% 2.51/0.70  fof(f3581,plain,(
% 2.51/0.70    ( ! [X8,X7] : (k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) = X7) )),
% 2.51/0.70    inference(forward_demodulation,[],[f56,f1344])).
% 2.51/0.70  fof(f56,plain,(
% 2.51/0.70    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7))) )),
% 2.51/0.70    inference(superposition,[],[f26,f23])).
% 2.51/0.70  fof(f23,plain,(
% 2.51/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.51/0.70    inference(cnf_transformation,[],[f4])).
% 2.51/0.70  fof(f4,axiom,(
% 2.51/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.51/0.70  fof(f26,plain,(
% 2.51/0.70    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 2.51/0.70    inference(cnf_transformation,[],[f6])).
% 2.51/0.70  fof(f6,axiom,(
% 2.51/0.70    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.51/0.70  fof(f2346,plain,(
% 2.51/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),X0)))) )),
% 2.51/0.70    inference(forward_demodulation,[],[f2345,f81])).
% 2.51/0.70  fof(f81,plain,(
% 2.51/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.51/0.70    inference(forward_demodulation,[],[f76,f39])).
% 2.51/0.70  fof(f76,plain,(
% 2.51/0.70    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.51/0.70    inference(superposition,[],[f26,f68])).
% 2.51/0.70  fof(f68,plain,(
% 2.51/0.70    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.51/0.70    inference(superposition,[],[f64,f22])).
% 2.51/0.70  fof(f22,plain,(
% 2.51/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.51/0.70    inference(cnf_transformation,[],[f1])).
% 2.51/0.70  fof(f1,axiom,(
% 2.51/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.51/0.70  fof(f64,plain,(
% 2.51/0.70    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.51/0.70    inference(forward_demodulation,[],[f58,f21])).
% 2.51/0.70  fof(f58,plain,(
% 2.51/0.70    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 2.51/0.70    inference(superposition,[],[f26,f21])).
% 2.51/0.70  fof(f2345,plain,(
% 2.51/0.70    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),X0)))) )),
% 2.51/0.70    inference(forward_demodulation,[],[f2331,f39])).
% 2.51/0.70  fof(f2331,plain,(
% 2.51/0.70    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK2)),X0)) )),
% 2.51/0.70    inference(superposition,[],[f37,f2029])).
% 2.51/0.70  fof(f2029,plain,(
% 2.51/0.70    k4_xboole_0(sK0,sK2) = k4_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK2))),
% 2.51/0.70    inference(superposition,[],[f94,f2014])).
% 2.51/0.70  fof(f2014,plain,(
% 2.51/0.70    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.51/0.70    inference(forward_demodulation,[],[f1988,f22])).
% 2.51/0.70  fof(f1988,plain,(
% 2.51/0.70    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 2.51/0.70    inference(superposition,[],[f1973,f23])).
% 2.51/0.70  fof(f1973,plain,(
% 2.51/0.70    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2)))) )),
% 2.51/0.70    inference(forward_demodulation,[],[f1940,f1927])).
% 2.51/0.70  fof(f1927,plain,(
% 2.51/0.70    ( ! [X4] : (k4_xboole_0(sK0,X4) = k4_xboole_0(sK0,k4_xboole_0(X4,k4_xboole_0(sK1,sK2)))) )),
% 2.51/0.70    inference(forward_demodulation,[],[f1895,f33])).
% 2.51/0.70  fof(f1895,plain,(
% 2.51/0.70    ( ! [X4] : (k4_xboole_0(sK0,k4_xboole_0(X4,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X4)))) )),
% 2.51/0.70    inference(superposition,[],[f33,f1533])).
% 2.51/0.70  fof(f1533,plain,(
% 2.51/0.70    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X1,k4_xboole_0(sK1,sK2))))) )),
% 2.51/0.70    inference(superposition,[],[f1521,f37])).
% 2.51/0.70  fof(f1521,plain,(
% 2.51/0.70    ( ! [X19] : (k4_xboole_0(sK0,X19) = k4_xboole_0(k4_xboole_0(sK0,X19),k4_xboole_0(sK1,sK2))) )),
% 2.51/0.70    inference(superposition,[],[f1344,f1486])).
% 2.51/0.70  fof(f1486,plain,(
% 2.51/0.70    ( ! [X4] : (k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X4))) )),
% 2.51/0.70    inference(forward_demodulation,[],[f1458,f21])).
% 2.51/0.70  fof(f1458,plain,(
% 2.51/0.70    ( ! [X4] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X4))) )),
% 2.51/0.70    inference(superposition,[],[f33,f1413])).
% 2.51/0.70  fof(f1413,plain,(
% 2.51/0.70    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X1)))) )),
% 2.51/0.70    inference(forward_demodulation,[],[f1412,f81])).
% 2.51/0.70  fof(f1412,plain,(
% 2.51/0.70    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X1)))) )),
% 2.51/0.70    inference(forward_demodulation,[],[f1400,f39])).
% 2.51/0.70  fof(f1400,plain,(
% 2.51/0.70    ( ! [X1] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),X1)) )),
% 2.51/0.70    inference(superposition,[],[f37,f1370])).
% 2.51/0.70  fof(f1370,plain,(
% 2.51/0.70    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 2.51/0.70    inference(superposition,[],[f1344,f418])).
% 2.51/0.70  fof(f418,plain,(
% 2.51/0.70    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.51/0.70    inference(forward_demodulation,[],[f400,f21])).
% 2.51/0.70  fof(f400,plain,(
% 2.51/0.70    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 2.51/0.70    inference(superposition,[],[f33,f336])).
% 2.51/0.70  fof(f336,plain,(
% 2.51/0.70    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 2.51/0.70    inference(resolution,[],[f36,f18])).
% 2.51/0.70  fof(f18,plain,(
% 2.51/0.70    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.51/0.70    inference(cnf_transformation,[],[f16])).
% 2.51/0.70  fof(f16,plain,(
% 2.51/0.70    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.51/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 2.51/0.70  fof(f15,plain,(
% 2.51/0.70    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 2.51/0.70    introduced(choice_axiom,[])).
% 2.51/0.70  fof(f14,plain,(
% 2.51/0.70    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.51/0.70    inference(ennf_transformation,[],[f13])).
% 2.51/0.70  fof(f13,negated_conjecture,(
% 2.51/0.70    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.51/0.70    inference(negated_conjecture,[],[f12])).
% 2.51/0.70  fof(f12,conjecture,(
% 2.51/0.70    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 2.51/0.70  fof(f36,plain,(
% 2.51/0.70    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.51/0.70    inference(definition_unfolding,[],[f28,f24])).
% 2.51/0.70  fof(f28,plain,(
% 2.51/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.51/0.70    inference(cnf_transformation,[],[f17])).
% 2.51/0.70  fof(f17,plain,(
% 2.51/0.70    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.51/0.70    inference(nnf_transformation,[],[f2])).
% 2.51/0.70  fof(f2,axiom,(
% 2.51/0.70    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.51/0.70  fof(f1940,plain,(
% 2.51/0.70    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2)))) )),
% 2.51/0.70    inference(superposition,[],[f1927,f26])).
% 2.51/0.70  fof(f94,plain,(
% 2.51/0.70    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k4_xboole_0(X7,X6),X6)) )),
% 2.51/0.70    inference(forward_demodulation,[],[f89,f53])).
% 2.51/0.70  fof(f53,plain,(
% 2.51/0.70    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3)) )),
% 2.51/0.70    inference(superposition,[],[f26,f22])).
% 2.51/0.70  fof(f89,plain,(
% 2.51/0.70    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k2_xboole_0(X6,X7),X6)) )),
% 2.51/0.70    inference(superposition,[],[f53,f23])).
% 2.51/0.70  fof(f37,plain,(
% 2.51/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 2.51/0.70    inference(definition_unfolding,[],[f30,f24,f24])).
% 2.51/0.70  fof(f30,plain,(
% 2.51/0.70    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.51/0.70    inference(cnf_transformation,[],[f9])).
% 2.51/0.70  fof(f9,axiom,(
% 2.51/0.70    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.51/0.70  fof(f33,plain,(
% 2.51/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.51/0.70    inference(definition_unfolding,[],[f25,f24])).
% 2.51/0.70  fof(f25,plain,(
% 2.51/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.51/0.70    inference(cnf_transformation,[],[f7])).
% 2.51/0.70  fof(f7,axiom,(
% 2.51/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.51/0.70  fof(f1344,plain,(
% 2.51/0.70    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X9,X8)) = X8) )),
% 2.51/0.70    inference(forward_demodulation,[],[f1313,f21])).
% 2.51/0.70  fof(f1313,plain,(
% 2.51/0.70    ( ! [X8,X9] : (k4_xboole_0(X8,k1_xboole_0) = k4_xboole_0(X8,k4_xboole_0(X9,X8))) )),
% 2.51/0.70    inference(superposition,[],[f33,f1026])).
% 2.51/0.70  fof(f1026,plain,(
% 2.51/0.70    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,X9)))) )),
% 2.51/0.70    inference(superposition,[],[f37,f457])).
% 2.51/0.70  fof(f457,plain,(
% 2.51/0.70    ( ! [X19,X18] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X18,X19),X18)) )),
% 2.51/0.70    inference(superposition,[],[f133,f34])).
% 2.51/0.70  fof(f34,plain,(
% 2.51/0.70    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.51/0.70    inference(definition_unfolding,[],[f27,f24])).
% 2.51/0.70  fof(f27,plain,(
% 2.51/0.70    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.51/0.70    inference(cnf_transformation,[],[f11])).
% 2.51/0.70  fof(f11,axiom,(
% 2.51/0.70    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.51/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.51/0.70  fof(f133,plain,(
% 2.51/0.70    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.51/0.70    inference(superposition,[],[f131,f22])).
% 2.51/0.70  fof(f131,plain,(
% 2.51/0.70    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 2.51/0.70    inference(forward_demodulation,[],[f129,f39])).
% 2.51/0.70  fof(f129,plain,(
% 2.51/0.70    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 2.51/0.70    inference(superposition,[],[f26,f96])).
% 2.51/0.70  fof(f96,plain,(
% 2.51/0.70    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 2.51/0.70    inference(forward_demodulation,[],[f91,f23])).
% 2.51/0.70  fof(f91,plain,(
% 2.51/0.70    ( ! [X2,X1] : (k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 2.51/0.70    inference(superposition,[],[f23,f53])).
% 2.51/0.70  fof(f335,plain,(
% 2.51/0.70    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 2.51/0.70    inference(resolution,[],[f35,f19])).
% 2.51/0.70  fof(f19,plain,(
% 2.51/0.70    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 2.51/0.70    inference(cnf_transformation,[],[f16])).
% 2.51/0.70  fof(f35,plain,(
% 2.51/0.70    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.51/0.70    inference(definition_unfolding,[],[f29,f24])).
% 2.51/0.70  fof(f29,plain,(
% 2.51/0.70    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.51/0.70    inference(cnf_transformation,[],[f17])).
% 2.51/0.70  % SZS output end Proof for theBenchmark
% 2.51/0.70  % (16676)------------------------------
% 2.51/0.70  % (16676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.70  % (16676)Termination reason: Refutation
% 2.51/0.70  
% 2.51/0.70  % (16676)Memory used [KB]: 9083
% 2.51/0.70  % (16676)Time elapsed: 0.279 s
% 2.51/0.70  % (16676)------------------------------
% 2.51/0.70  % (16676)------------------------------
% 2.51/0.70  % (16668)Success in time 0.344 s
%------------------------------------------------------------------------------
