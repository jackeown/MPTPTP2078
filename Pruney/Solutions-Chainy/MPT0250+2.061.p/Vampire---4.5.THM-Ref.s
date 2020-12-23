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
% DateTime   : Thu Dec  3 12:38:28 EST 2020

% Result     : Theorem 3.97s
% Output     : Refutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 593 expanded)
%              Number of leaves         :   19 ( 193 expanded)
%              Depth                    :   26
%              Number of atoms          :  121 ( 679 expanded)
%              Number of equality atoms :   56 ( 510 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3604,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3603,f148])).

fof(f148,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f143,f29])).

fof(f29,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f143,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r1_tarski(sK1,sK1) ),
    inference(superposition,[],[f62,f135])).

fof(f135,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f125,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f125,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),sK1))
    | sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f85,f28])).

fof(f28,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | X2 = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f53,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f35,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f62,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_xboole_0(k1_tarski(X0),X1)) ),
    inference(superposition,[],[f58,f30])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2)) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f3603,plain,(
    r1_tarski(sK1,sK1) ),
    inference(backward_demodulation,[],[f3596,f3598])).

fof(f3598,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f3596,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X0)
      | k2_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f85,f31])).

fof(f3596,plain,(
    r1_tarski(k2_xboole_0(sK1,k1_tarski(sK0)),sK1) ),
    inference(backward_demodulation,[],[f28,f3590])).

fof(f3590,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f3491,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f3491,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f33,f3477])).

fof(f3477,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(subsumption_resolution,[],[f3470,f3454])).

fof(f3454,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X1,X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f3389,f34])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f3389,plain,(
    ! [X12,X13,X11] : r1_tarski(k2_tarski(X11,X13),k1_enumset1(X13,X12,X11)) ),
    inference(superposition,[],[f3370,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0) ),
    inference(superposition,[],[f41,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f3370,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X2,X3,X1)) ),
    inference(forward_demodulation,[],[f3366,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f3366,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k2_tarski(X0,X1),k3_enumset1(X0,X0,X2,X3,X1)) ),
    inference(superposition,[],[f3363,f34])).

fof(f3363,plain,(
    ! [X4,X2,X0,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X3,X4,X2)) ),
    inference(forward_demodulation,[],[f3358,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f3358,plain,(
    ! [X4,X2,X0,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k4_enumset1(X0,X0,X1,X3,X4,X2)) ),
    inference(superposition,[],[f544,f36])).

fof(f544,plain,(
    ! [X61,X66,X64,X62,X65,X63] : r1_tarski(k2_enumset1(X61,X62,X63,X64),k4_enumset1(X61,X62,X63,X66,X65,X64)) ),
    inference(superposition,[],[f336,f340])).

fof(f340,plain,(
    ! [X24,X23,X21,X25,X22,X20] : k5_enumset1(X23,X24,X25,X20,X21,X22,X22) = k4_enumset1(X23,X24,X25,X22,X21,X20) ),
    inference(backward_demodulation,[],[f239,f337])).

fof(f337,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(forward_demodulation,[],[f324,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f324,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(superposition,[],[f317,f36])).

fof(f317,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) = k5_enumset1(X3,X4,X5,X6,X0,X1,X2) ),
    inference(backward_demodulation,[],[f94,f311])).

fof(f311,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X4,X5,X6) ),
    inference(forward_demodulation,[],[f305,f45])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f305,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X4,X5,X6) ),
    inference(superposition,[],[f134,f120])).

fof(f120,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(forward_demodulation,[],[f113,f46])).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f113,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(superposition,[],[f48,f42])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(f134,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) = k6_enumset1(X3,X4,X5,X6,X7,X0,X1,X2) ),
    inference(backward_demodulation,[],[f114,f133])).

fof(f133,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(forward_demodulation,[],[f128,f120])).

fof(f128,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(superposition,[],[f49,f43])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

fof(f114,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f48,f36])).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f46,f36])).

fof(f239,plain,(
    ! [X24,X23,X21,X25,X22,X20] : k5_enumset1(X23,X24,X25,X20,X21,X22,X22) = k2_xboole_0(k1_enumset1(X23,X24,X25),k1_enumset1(X22,X21,X20)) ),
    inference(superposition,[],[f101,f76])).

fof(f101,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(forward_demodulation,[],[f91,f45])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(superposition,[],[f46,f36])).

fof(f336,plain,(
    ! [X47,X45,X43,X41,X46,X44,X42] : r1_tarski(k2_enumset1(X41,X42,X43,X44),k5_enumset1(X41,X42,X43,X44,X45,X46,X47)) ),
    inference(superposition,[],[f31,f317])).

fof(f3470,plain,(
    ! [X4,X5] :
      ( k2_tarski(X4,X5) = k2_tarski(X5,X4)
      | ~ r1_tarski(k2_tarski(X4,X5),k2_tarski(X5,X4)) ) ),
    inference(resolution,[],[f3454,f85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:25:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (27029)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.43  % (27021)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (27022)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (27016)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (27018)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (27014)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (27024)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (27026)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (27023)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (27015)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (27020)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (27019)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (27025)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (27031)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (27025)Refutation not found, incomplete strategy% (27025)------------------------------
% 0.21/0.51  % (27025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27025)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27025)Memory used [KB]: 10618
% 0.21/0.51  % (27025)Time elapsed: 0.052 s
% 0.21/0.51  % (27025)------------------------------
% 0.21/0.51  % (27025)------------------------------
% 0.21/0.51  % (27030)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (27028)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (27027)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (27017)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 3.97/0.87  % (27017)Refutation found. Thanks to Tanya!
% 3.97/0.87  % SZS status Theorem for theBenchmark
% 3.97/0.88  % SZS output start Proof for theBenchmark
% 3.97/0.88  fof(f3604,plain,(
% 3.97/0.88    $false),
% 3.97/0.88    inference(subsumption_resolution,[],[f3603,f148])).
% 3.97/0.88  fof(f148,plain,(
% 3.97/0.88    ~r1_tarski(sK1,sK1)),
% 3.97/0.88    inference(subsumption_resolution,[],[f143,f29])).
% 3.97/0.88  fof(f29,plain,(
% 3.97/0.88    ~r2_hidden(sK0,sK1)),
% 3.97/0.88    inference(cnf_transformation,[],[f25])).
% 3.97/0.88  fof(f25,plain,(
% 3.97/0.88    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 3.97/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 3.97/0.88  fof(f24,plain,(
% 3.97/0.88    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 3.97/0.88    introduced(choice_axiom,[])).
% 3.97/0.88  fof(f21,plain,(
% 3.97/0.88    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 3.97/0.88    inference(ennf_transformation,[],[f20])).
% 3.97/0.88  fof(f20,negated_conjecture,(
% 3.97/0.88    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.97/0.88    inference(negated_conjecture,[],[f19])).
% 3.97/0.88  fof(f19,conjecture,(
% 3.97/0.88    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 3.97/0.88  fof(f143,plain,(
% 3.97/0.88    r2_hidden(sK0,sK1) | ~r1_tarski(sK1,sK1)),
% 3.97/0.88    inference(superposition,[],[f62,f135])).
% 3.97/0.88  fof(f135,plain,(
% 3.97/0.88    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~r1_tarski(sK1,sK1)),
% 3.97/0.88    inference(resolution,[],[f125,f37])).
% 3.97/0.88  fof(f37,plain,(
% 3.97/0.88    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f23])).
% 3.97/0.88  fof(f23,plain,(
% 3.97/0.88    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.97/0.88    inference(ennf_transformation,[],[f2])).
% 3.97/0.88  fof(f2,axiom,(
% 3.97/0.88    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 3.97/0.88  fof(f125,plain,(
% 3.97/0.88    ~r1_tarski(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) | sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 3.97/0.88    inference(resolution,[],[f85,f28])).
% 3.97/0.88  fof(f28,plain,(
% 3.97/0.88    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 3.97/0.88    inference(cnf_transformation,[],[f25])).
% 3.97/0.88  fof(f85,plain,(
% 3.97/0.88    ( ! [X2,X3] : (~r1_tarski(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3)) )),
% 3.97/0.88    inference(superposition,[],[f53,f35])).
% 3.97/0.88  fof(f35,plain,(
% 3.97/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f22])).
% 3.97/0.88  fof(f22,plain,(
% 3.97/0.88    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.97/0.88    inference(ennf_transformation,[],[f3])).
% 3.97/0.88  fof(f3,axiom,(
% 3.97/0.88    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.97/0.88  fof(f53,plain,(
% 3.97/0.88    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 3.97/0.88    inference(superposition,[],[f35,f32])).
% 3.97/0.88  fof(f32,plain,(
% 3.97/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f1])).
% 3.97/0.88  fof(f1,axiom,(
% 3.97/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.97/0.88  fof(f62,plain,(
% 3.97/0.88    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(k1_tarski(X0),X1))) )),
% 3.97/0.88    inference(superposition,[],[f58,f30])).
% 3.97/0.88  fof(f30,plain,(
% 3.97/0.88    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f10])).
% 3.97/0.88  fof(f10,axiom,(
% 3.97/0.88    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.97/0.88  fof(f58,plain,(
% 3.97/0.88    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(k2_tarski(X0,X1),X2))) )),
% 3.97/0.88    inference(resolution,[],[f38,f31])).
% 3.97/0.88  fof(f31,plain,(
% 3.97/0.88    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.97/0.88    inference(cnf_transformation,[],[f4])).
% 3.97/0.88  fof(f4,axiom,(
% 3.97/0.88    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.97/0.88  fof(f38,plain,(
% 3.97/0.88    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f27])).
% 3.97/0.88  fof(f27,plain,(
% 3.97/0.88    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.97/0.88    inference(flattening,[],[f26])).
% 3.97/0.88  fof(f26,plain,(
% 3.97/0.88    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.97/0.88    inference(nnf_transformation,[],[f18])).
% 3.97/0.88  fof(f18,axiom,(
% 3.97/0.88    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 3.97/0.88  fof(f3603,plain,(
% 3.97/0.88    r1_tarski(sK1,sK1)),
% 3.97/0.88    inference(backward_demodulation,[],[f3596,f3598])).
% 3.97/0.88  fof(f3598,plain,(
% 3.97/0.88    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 3.97/0.88    inference(resolution,[],[f3596,f121])).
% 3.97/0.88  fof(f121,plain,(
% 3.97/0.88    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X0) | k2_xboole_0(X0,X1) = X0) )),
% 3.97/0.88    inference(resolution,[],[f85,f31])).
% 3.97/0.88  fof(f3596,plain,(
% 3.97/0.88    r1_tarski(k2_xboole_0(sK1,k1_tarski(sK0)),sK1)),
% 3.97/0.88    inference(backward_demodulation,[],[f28,f3590])).
% 3.97/0.88  fof(f3590,plain,(
% 3.97/0.88    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 3.97/0.88    inference(superposition,[],[f3491,f33])).
% 3.97/0.88  fof(f33,plain,(
% 3.97/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.97/0.88    inference(cnf_transformation,[],[f17])).
% 3.97/0.88  fof(f17,axiom,(
% 3.97/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.97/0.88  fof(f3491,plain,(
% 3.97/0.88    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 3.97/0.88    inference(superposition,[],[f33,f3477])).
% 3.97/0.88  fof(f3477,plain,(
% 3.97/0.88    ( ! [X4,X5] : (k2_tarski(X4,X5) = k2_tarski(X5,X4)) )),
% 3.97/0.88    inference(subsumption_resolution,[],[f3470,f3454])).
% 3.97/0.88  fof(f3454,plain,(
% 3.97/0.88    ( ! [X0,X1] : (r1_tarski(k2_tarski(X1,X0),k2_tarski(X0,X1))) )),
% 3.97/0.88    inference(superposition,[],[f3389,f34])).
% 3.97/0.88  fof(f34,plain,(
% 3.97/0.88    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f11])).
% 3.97/0.88  fof(f11,axiom,(
% 3.97/0.88    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.97/0.88  fof(f3389,plain,(
% 3.97/0.88    ( ! [X12,X13,X11] : (r1_tarski(k2_tarski(X11,X13),k1_enumset1(X13,X12,X11))) )),
% 3.97/0.88    inference(superposition,[],[f3370,f76])).
% 3.97/0.88  fof(f76,plain,(
% 3.97/0.88    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0)) )),
% 3.97/0.88    inference(superposition,[],[f41,f36])).
% 3.97/0.88  fof(f36,plain,(
% 3.97/0.88    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f12])).
% 3.97/0.88  fof(f12,axiom,(
% 3.97/0.88    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.97/0.88  fof(f41,plain,(
% 3.97/0.88    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f6])).
% 3.97/0.88  fof(f6,axiom,(
% 3.97/0.88    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 3.97/0.88  fof(f3370,plain,(
% 3.97/0.88    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X2,X3,X1))) )),
% 3.97/0.88    inference(forward_demodulation,[],[f3366,f42])).
% 3.97/0.88  fof(f42,plain,(
% 3.97/0.88    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f13])).
% 3.97/0.88  fof(f13,axiom,(
% 3.97/0.88    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.97/0.88  fof(f3366,plain,(
% 3.97/0.88    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_tarski(X0,X1),k3_enumset1(X0,X0,X2,X3,X1))) )),
% 3.97/0.88    inference(superposition,[],[f3363,f34])).
% 3.97/0.88  fof(f3363,plain,(
% 3.97/0.88    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X3,X4,X2))) )),
% 3.97/0.88    inference(forward_demodulation,[],[f3358,f43])).
% 3.97/0.88  fof(f43,plain,(
% 3.97/0.88    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f14])).
% 3.97/0.88  fof(f14,axiom,(
% 3.97/0.88    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.97/0.88  fof(f3358,plain,(
% 3.97/0.88    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k4_enumset1(X0,X0,X1,X3,X4,X2))) )),
% 3.97/0.88    inference(superposition,[],[f544,f36])).
% 3.97/0.88  fof(f544,plain,(
% 3.97/0.88    ( ! [X61,X66,X64,X62,X65,X63] : (r1_tarski(k2_enumset1(X61,X62,X63,X64),k4_enumset1(X61,X62,X63,X66,X65,X64))) )),
% 3.97/0.88    inference(superposition,[],[f336,f340])).
% 3.97/0.88  fof(f340,plain,(
% 3.97/0.88    ( ! [X24,X23,X21,X25,X22,X20] : (k5_enumset1(X23,X24,X25,X20,X21,X22,X22) = k4_enumset1(X23,X24,X25,X22,X21,X20)) )),
% 3.97/0.88    inference(backward_demodulation,[],[f239,f337])).
% 3.97/0.88  fof(f337,plain,(
% 3.97/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 3.97/0.88    inference(forward_demodulation,[],[f324,f44])).
% 3.97/0.88  fof(f44,plain,(
% 3.97/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f15])).
% 3.97/0.88  fof(f15,axiom,(
% 3.97/0.88    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.97/0.88  fof(f324,plain,(
% 3.97/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 3.97/0.88    inference(superposition,[],[f317,f36])).
% 3.97/0.88  fof(f317,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2)) = k5_enumset1(X3,X4,X5,X6,X0,X1,X2)) )),
% 3.97/0.88    inference(backward_demodulation,[],[f94,f311])).
% 3.97/0.88  fof(f311,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X4,X5,X6)) )),
% 3.97/0.88    inference(forward_demodulation,[],[f305,f45])).
% 3.97/0.88  fof(f45,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.97/0.88    inference(cnf_transformation,[],[f16])).
% 3.97/0.88  fof(f16,axiom,(
% 3.97/0.88    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.97/0.88  fof(f305,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X4,X5,X6)) )),
% 3.97/0.88    inference(superposition,[],[f134,f120])).
% 3.97/0.88  fof(f120,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.97/0.88    inference(forward_demodulation,[],[f113,f46])).
% 3.97/0.88  fof(f46,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 3.97/0.88    inference(cnf_transformation,[],[f5])).
% 3.97/0.88  fof(f5,axiom,(
% 3.97/0.88    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 3.97/0.88  fof(f113,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.97/0.88    inference(superposition,[],[f48,f42])).
% 3.97/0.88  fof(f48,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 3.97/0.88    inference(cnf_transformation,[],[f7])).
% 3.97/0.88  fof(f7,axiom,(
% 3.97/0.88    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
% 3.97/0.88  fof(f134,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) = k6_enumset1(X3,X4,X5,X6,X7,X0,X1,X2)) )),
% 3.97/0.88    inference(backward_demodulation,[],[f114,f133])).
% 3.97/0.88  fof(f133,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 3.97/0.88    inference(forward_demodulation,[],[f128,f120])).
% 3.97/0.88  fof(f128,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X0,X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 3.97/0.88    inference(superposition,[],[f49,f43])).
% 3.97/0.88  fof(f49,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 3.97/0.88    inference(cnf_transformation,[],[f8])).
% 3.97/0.88  fof(f8,axiom,(
% 3.97/0.88    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 3.97/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).
% 3.97/0.88  fof(f114,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k7_enumset1(X3,X4,X5,X6,X7,X0,X0,X1,X2) = k2_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_enumset1(X0,X1,X2))) )),
% 3.97/0.88    inference(superposition,[],[f48,f36])).
% 3.97/0.88  fof(f94,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X3,X4,X5,X6,X0,X0,X1,X2) = k2_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_enumset1(X0,X1,X2))) )),
% 3.97/0.88    inference(superposition,[],[f46,f36])).
% 3.97/0.88  fof(f239,plain,(
% 3.97/0.88    ( ! [X24,X23,X21,X25,X22,X20] : (k5_enumset1(X23,X24,X25,X20,X21,X22,X22) = k2_xboole_0(k1_enumset1(X23,X24,X25),k1_enumset1(X22,X21,X20))) )),
% 3.97/0.88    inference(superposition,[],[f101,f76])).
% 3.97/0.88  fof(f101,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 3.97/0.88    inference(forward_demodulation,[],[f91,f45])).
% 3.97/0.88  fof(f91,plain,(
% 3.97/0.88    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 3.97/0.88    inference(superposition,[],[f46,f36])).
% 3.97/0.88  fof(f336,plain,(
% 3.97/0.88    ( ! [X47,X45,X43,X41,X46,X44,X42] : (r1_tarski(k2_enumset1(X41,X42,X43,X44),k5_enumset1(X41,X42,X43,X44,X45,X46,X47))) )),
% 3.97/0.88    inference(superposition,[],[f31,f317])).
% 3.97/0.88  fof(f3470,plain,(
% 3.97/0.88    ( ! [X4,X5] : (k2_tarski(X4,X5) = k2_tarski(X5,X4) | ~r1_tarski(k2_tarski(X4,X5),k2_tarski(X5,X4))) )),
% 3.97/0.88    inference(resolution,[],[f3454,f85])).
% 3.97/0.88  % SZS output end Proof for theBenchmark
% 3.97/0.88  % (27017)------------------------------
% 3.97/0.88  % (27017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/0.88  % (27017)Termination reason: Refutation
% 3.97/0.88  
% 3.97/0.88  % (27017)Memory used [KB]: 3965
% 3.97/0.88  % (27017)Time elapsed: 0.422 s
% 3.97/0.88  % (27017)------------------------------
% 3.97/0.88  % (27017)------------------------------
% 4.05/0.89  % (27013)Success in time 0.529 s
%------------------------------------------------------------------------------
