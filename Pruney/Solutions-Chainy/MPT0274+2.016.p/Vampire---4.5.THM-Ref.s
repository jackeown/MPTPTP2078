%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:22 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 451 expanded)
%              Number of leaves         :   19 ( 142 expanded)
%              Depth                    :   17
%              Number of atoms          :  151 ( 668 expanded)
%              Number of equality atoms :   66 ( 406 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1452,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1451,f826])).

fof(f826,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f824,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k2_tarski(X0,X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f59,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f824,plain,
    ( r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f760,f37])).

fof(f37,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f760,plain,(
    ! [X4,X3] : r1_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f753,f545])).

fof(f545,plain,(
    ! [X21,X22] : k5_xboole_0(X22,k2_xboole_0(X21,X22)) = k4_xboole_0(X21,X22) ),
    inference(forward_demodulation,[],[f529,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f529,plain,(
    ! [X21,X22] : k5_xboole_0(X22,k2_xboole_0(X21,X22)) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(superposition,[],[f168,f153])).

fof(f153,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f57,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f168,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f145,f66])).

fof(f66,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f46,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f145,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f57,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f753,plain,(
    ! [X4,X3] : r1_xboole_0(X3,k5_xboole_0(X3,k2_xboole_0(X4,X3))) ),
    inference(superposition,[],[f243,f209])).

fof(f209,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f82,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f82,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f243,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f239,f46])).

fof(f239,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(k2_xboole_0(X0,X1),X0)) ),
    inference(superposition,[],[f73,f231])).

fof(f231,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(backward_demodulation,[],[f113,f215])).

fof(f215,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f172,f168])).

fof(f172,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f168,f46])).

fof(f113,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f52,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f73,plain,(
    ! [X2,X3] : r1_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f47,f46])).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f1451,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f1449,f825])).

fof(f825,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f823,f253])).

fof(f253,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_xboole_0(X4,k2_tarski(X3,X2))
      | ~ r2_hidden(X2,X4) ) ),
    inference(superposition,[],[f86,f45])).

fof(f823,plain,
    ( r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f760,f38])).

fof(f38,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f1449,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f1448,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f1448,plain,(
    ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f1447,f825])).

fof(f1447,plain,
    ( r2_hidden(sK1,sK2)
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f1446,f826])).

fof(f1446,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f1445])).

fof(f1445,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f39,f1418])).

fof(f1418,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(backward_demodulation,[],[f54,f1416])).

fof(f1416,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),X3) ),
    inference(forward_demodulation,[],[f1415,f545])).

fof(f1415,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),X3) ),
    inference(forward_demodulation,[],[f1387,f46])).

fof(f1387,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),X3) = k5_xboole_0(k2_xboole_0(X2,X3),X3) ),
    inference(superposition,[],[f50,f1340])).

fof(f1340,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f1284,f216])).

fof(f216,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f172,f172])).

fof(f1284,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),X0) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X1,X0),X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f134,f84])).

fof(f84,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f81,f41])).

fof(f41,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f81,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f49,f43])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f134,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),X4) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X3),X4),k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f52,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f39,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (24340)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (24332)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (24341)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (24329)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (24330)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (24335)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (24334)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (24331)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (24345)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (24337)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (24342)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (24327)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (24333)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (24338)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (24344)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (24338)Refutation not found, incomplete strategy% (24338)------------------------------
% 0.20/0.50  % (24338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24338)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24338)Memory used [KB]: 10618
% 0.20/0.50  % (24338)Time elapsed: 0.089 s
% 0.20/0.50  % (24338)------------------------------
% 0.20/0.50  % (24338)------------------------------
% 0.20/0.50  % (24336)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (24328)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (24343)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.80/0.59  % (24330)Refutation found. Thanks to Tanya!
% 1.80/0.59  % SZS status Theorem for theBenchmark
% 1.80/0.59  % SZS output start Proof for theBenchmark
% 1.80/0.59  fof(f1452,plain,(
% 1.80/0.59    $false),
% 1.80/0.59    inference(subsumption_resolution,[],[f1451,f826])).
% 1.80/0.59  fof(f826,plain,(
% 1.80/0.59    ~r2_hidden(sK0,sK2)),
% 1.80/0.59    inference(subsumption_resolution,[],[f824,f86])).
% 1.80/0.59  fof(f86,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k2_tarski(X0,X2)) | ~r2_hidden(X0,X1)) )),
% 1.80/0.59    inference(resolution,[],[f59,f53])).
% 1.80/0.59  fof(f53,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f29])).
% 1.80/0.59  fof(f29,plain,(
% 1.80/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.80/0.59    inference(ennf_transformation,[],[f3])).
% 1.80/0.59  fof(f3,axiom,(
% 1.80/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.80/0.59  fof(f59,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f32])).
% 1.80/0.59  fof(f32,plain,(
% 1.80/0.59    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.80/0.59    inference(ennf_transformation,[],[f23])).
% 1.80/0.59  fof(f23,axiom,(
% 1.80/0.59    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.80/0.59  fof(f824,plain,(
% 1.80/0.59    r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 1.80/0.59    inference(superposition,[],[f760,f37])).
% 1.80/0.59  fof(f37,plain,(
% 1.80/0.59    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,sK2)),
% 1.80/0.59    inference(cnf_transformation,[],[f36])).
% 1.80/0.59  fof(f36,plain,(
% 1.80/0.59    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.80/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f35])).
% 1.80/0.59  fof(f35,plain,(
% 1.80/0.59    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 1.80/0.59    introduced(choice_axiom,[])).
% 1.80/0.59  fof(f34,plain,(
% 1.80/0.59    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.80/0.59    inference(flattening,[],[f33])).
% 1.80/0.59  fof(f33,plain,(
% 1.80/0.59    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.80/0.59    inference(nnf_transformation,[],[f28])).
% 1.80/0.59  fof(f28,plain,(
% 1.80/0.59    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.80/0.59    inference(ennf_transformation,[],[f26])).
% 1.80/0.59  fof(f26,negated_conjecture,(
% 1.80/0.59    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.80/0.59    inference(negated_conjecture,[],[f25])).
% 1.80/0.59  fof(f25,conjecture,(
% 1.80/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.80/0.59  fof(f760,plain,(
% 1.80/0.59    ( ! [X4,X3] : (r1_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 1.80/0.59    inference(forward_demodulation,[],[f753,f545])).
% 1.80/0.59  fof(f545,plain,(
% 1.80/0.59    ( ! [X21,X22] : (k5_xboole_0(X22,k2_xboole_0(X21,X22)) = k4_xboole_0(X21,X22)) )),
% 1.80/0.59    inference(forward_demodulation,[],[f529,f50])).
% 1.80/0.59  fof(f50,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f5])).
% 1.80/0.59  fof(f5,axiom,(
% 1.80/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.80/0.59  fof(f529,plain,(
% 1.80/0.59    ( ! [X21,X22] : (k5_xboole_0(X22,k2_xboole_0(X21,X22)) = k5_xboole_0(X21,k3_xboole_0(X21,X22))) )),
% 1.80/0.59    inference(superposition,[],[f168,f153])).
% 1.80/0.59  fof(f153,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 1.80/0.59    inference(superposition,[],[f57,f52])).
% 1.80/0.59  fof(f52,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f12])).
% 1.80/0.59  fof(f12,axiom,(
% 1.80/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.80/0.59  fof(f57,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f10])).
% 1.80/0.59  fof(f10,axiom,(
% 1.80/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.80/0.59  fof(f168,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.80/0.59    inference(forward_demodulation,[],[f145,f66])).
% 1.80/0.59  fof(f66,plain,(
% 1.80/0.59    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.80/0.59    inference(superposition,[],[f46,f42])).
% 1.80/0.59  fof(f42,plain,(
% 1.80/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.80/0.59    inference(cnf_transformation,[],[f7])).
% 1.80/0.59  fof(f7,axiom,(
% 1.80/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.80/0.59  fof(f46,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f1])).
% 1.80/0.59  fof(f1,axiom,(
% 1.80/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.80/0.59  fof(f145,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(superposition,[],[f57,f40])).
% 1.80/0.59  fof(f40,plain,(
% 1.80/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f11])).
% 1.80/0.59  fof(f11,axiom,(
% 1.80/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.80/0.59  fof(f753,plain,(
% 1.80/0.59    ( ! [X4,X3] : (r1_xboole_0(X3,k5_xboole_0(X3,k2_xboole_0(X4,X3)))) )),
% 1.80/0.59    inference(superposition,[],[f243,f209])).
% 1.80/0.59  fof(f209,plain,(
% 1.80/0.59    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.80/0.59    inference(superposition,[],[f82,f49])).
% 1.80/0.59  fof(f49,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f21])).
% 1.80/0.59  fof(f21,axiom,(
% 1.80/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.80/0.59  fof(f82,plain,(
% 1.80/0.59    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 1.80/0.59    inference(superposition,[],[f49,f45])).
% 1.80/0.59  fof(f45,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f13])).
% 1.80/0.59  fof(f13,axiom,(
% 1.80/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.80/0.59  fof(f243,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 1.80/0.59    inference(forward_demodulation,[],[f239,f46])).
% 1.80/0.59  fof(f239,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(k2_xboole_0(X0,X1),X0))) )),
% 1.80/0.59    inference(superposition,[],[f73,f231])).
% 1.80/0.59  fof(f231,plain,(
% 1.80/0.59    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1) )),
% 1.80/0.59    inference(backward_demodulation,[],[f113,f215])).
% 1.80/0.59  fof(f215,plain,(
% 1.80/0.59    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 1.80/0.59    inference(superposition,[],[f172,f168])).
% 1.80/0.59  fof(f172,plain,(
% 1.80/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.80/0.59    inference(superposition,[],[f168,f46])).
% 1.80/0.59  fof(f113,plain,(
% 1.80/0.59    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) )),
% 1.80/0.59    inference(superposition,[],[f52,f51])).
% 1.80/0.59  fof(f51,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f8])).
% 1.80/0.59  fof(f8,axiom,(
% 1.80/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 1.80/0.59  fof(f73,plain,(
% 1.80/0.59    ( ! [X2,X3] : (r1_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 1.80/0.59    inference(superposition,[],[f47,f46])).
% 1.80/0.59  fof(f47,plain,(
% 1.80/0.59    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f4])).
% 1.80/0.59  fof(f4,axiom,(
% 1.80/0.59    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.80/0.59  fof(f1451,plain,(
% 1.80/0.59    r2_hidden(sK0,sK2)),
% 1.80/0.59    inference(subsumption_resolution,[],[f1449,f825])).
% 1.80/0.59  fof(f825,plain,(
% 1.80/0.59    ~r2_hidden(sK1,sK2)),
% 1.80/0.59    inference(subsumption_resolution,[],[f823,f253])).
% 1.80/0.59  fof(f253,plain,(
% 1.80/0.59    ( ! [X4,X2,X3] : (~r1_xboole_0(X4,k2_tarski(X3,X2)) | ~r2_hidden(X2,X4)) )),
% 1.80/0.59    inference(superposition,[],[f86,f45])).
% 1.80/0.59  fof(f823,plain,(
% 1.80/0.59    r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 1.80/0.59    inference(superposition,[],[f760,f38])).
% 1.80/0.59  fof(f38,plain,(
% 1.80/0.59    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 1.80/0.59    inference(cnf_transformation,[],[f36])).
% 1.80/0.59  fof(f1449,plain,(
% 1.80/0.59    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 1.80/0.59    inference(resolution,[],[f1448,f58])).
% 1.80/0.59  fof(f58,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f31])).
% 1.80/0.59  fof(f31,plain,(
% 1.80/0.59    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 1.80/0.59    inference(ennf_transformation,[],[f24])).
% 1.80/0.59  fof(f24,axiom,(
% 1.80/0.59    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 1.80/0.59  fof(f1448,plain,(
% 1.80/0.59    ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.80/0.59    inference(subsumption_resolution,[],[f1447,f825])).
% 1.80/0.59  fof(f1447,plain,(
% 1.80/0.59    r2_hidden(sK1,sK2) | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.80/0.59    inference(subsumption_resolution,[],[f1446,f826])).
% 1.80/0.59  fof(f1446,plain,(
% 1.80/0.59    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.80/0.59    inference(trivial_inequality_removal,[],[f1445])).
% 1.80/0.59  fof(f1445,plain,(
% 1.80/0.59    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.80/0.59    inference(superposition,[],[f39,f1418])).
% 1.80/0.59  fof(f1418,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.80/0.59    inference(backward_demodulation,[],[f54,f1416])).
% 1.80/0.59  fof(f1416,plain,(
% 1.80/0.59    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),X3)) )),
% 1.80/0.59    inference(forward_demodulation,[],[f1415,f545])).
% 1.80/0.59  fof(f1415,plain,(
% 1.80/0.59    ( ! [X2,X3] : (k5_xboole_0(X3,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),X3)) )),
% 1.80/0.59    inference(forward_demodulation,[],[f1387,f46])).
% 1.80/0.59  fof(f1387,plain,(
% 1.80/0.59    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),X3) = k5_xboole_0(k2_xboole_0(X2,X3),X3)) )),
% 1.80/0.59    inference(superposition,[],[f50,f1340])).
% 1.80/0.59  fof(f1340,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0) )),
% 1.80/0.59    inference(forward_demodulation,[],[f1284,f216])).
% 1.80/0.59  fof(f216,plain,(
% 1.80/0.59    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 1.80/0.59    inference(superposition,[],[f172,f172])).
% 1.80/0.59  fof(f1284,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X1,X0),X0) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X1,X0),X0),k2_xboole_0(X1,X0))) )),
% 1.80/0.59    inference(superposition,[],[f134,f84])).
% 1.80/0.59  fof(f84,plain,(
% 1.80/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.80/0.59    inference(forward_demodulation,[],[f81,f41])).
% 1.80/0.59  fof(f41,plain,(
% 1.80/0.59    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.80/0.59    inference(cnf_transformation,[],[f22])).
% 1.80/0.59  fof(f22,axiom,(
% 1.80/0.59    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 1.80/0.59  fof(f81,plain,(
% 1.80/0.59    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0)) )),
% 1.80/0.59    inference(superposition,[],[f49,f43])).
% 1.80/0.59  fof(f43,plain,(
% 1.80/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f14])).
% 1.80/0.59  fof(f14,axiom,(
% 1.80/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.80/0.59  fof(f134,plain,(
% 1.80/0.59    ( ! [X4,X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),X4) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X2,X3),X4),k2_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 1.80/0.59    inference(superposition,[],[f52,f56])).
% 1.80/0.59  fof(f56,plain,(
% 1.80/0.59    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.80/0.59    inference(cnf_transformation,[],[f6])).
% 1.80/0.59  fof(f6,axiom,(
% 1.80/0.59    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.80/0.59  fof(f54,plain,(
% 1.80/0.59    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.80/0.59    inference(cnf_transformation,[],[f30])).
% 1.80/0.59  fof(f30,plain,(
% 1.80/0.59    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.80/0.59    inference(ennf_transformation,[],[f9])).
% 1.80/0.59  fof(f9,axiom,(
% 1.80/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 1.80/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 1.80/0.59  fof(f39,plain,(
% 1.80/0.59    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 1.80/0.59    inference(cnf_transformation,[],[f36])).
% 1.80/0.59  % SZS output end Proof for theBenchmark
% 1.80/0.59  % (24330)------------------------------
% 1.80/0.59  % (24330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.59  % (24330)Termination reason: Refutation
% 1.80/0.59  
% 1.80/0.59  % (24330)Memory used [KB]: 3326
% 1.80/0.59  % (24330)Time elapsed: 0.160 s
% 1.80/0.59  % (24330)------------------------------
% 1.80/0.59  % (24330)------------------------------
% 1.80/0.59  % (24323)Success in time 0.236 s
%------------------------------------------------------------------------------
