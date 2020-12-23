%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:56 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 952 expanded)
%              Number of leaves         :   20 ( 274 expanded)
%              Depth                    :   22
%              Number of atoms          :  156 (1685 expanded)
%              Number of equality atoms :   99 ( 998 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f871,plain,(
    $false ),
    inference(subsumption_resolution,[],[f870,f111])).

fof(f111,plain,(
    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f66,f30])).

fof(f30,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f870,plain,(
    ~ r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(subsumption_resolution,[],[f866,f146])).

fof(f146,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f62,f143])).

fof(f143,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f142,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f82,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f79,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(resolution,[],[f68,f71])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f49,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f142,plain,(
    ! [X1] : k5_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f125,f138])).

fof(f138,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f124,f62])).

fof(f124,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f60,f79])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f38,f39,f39])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f125,plain,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k3_xboole_0(X1,X1)) ),
    inference(superposition,[],[f60,f62])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f866,plain,
    ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | ~ r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(superposition,[],[f795,f275])).

fof(f275,plain,(
    ! [X2,X1] :
      ( k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f274,f146])).

fof(f274,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X2,k1_xboole_0) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f273,f143])).

fof(f273,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f272,f145])).

fof(f145,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(backward_demodulation,[],[f91,f143])).

fof(f91,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(superposition,[],[f52,f62])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f272,plain,(
    ! [X2,X1] :
      ( k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0)))
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f271,f52])).

fof(f271,plain,(
    ! [X2,X1] :
      ( k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) = k5_xboole_0(k5_xboole_0(X2,k1_xboole_0),k3_xboole_0(X2,k1_xboole_0))
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f270,f65])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f270,plain,(
    ! [X2,X1] :
      ( k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k1_xboole_0))
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f254,f84])).

fof(f254,plain,(
    ! [X2,X1] :
      ( k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k5_xboole_0(X1,X1)))
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f64,f42])).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f40,f58,f39,f58])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f795,plain,(
    sK1 != k5_xboole_0(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f466,f794])).

fof(f794,plain,(
    ! [X6,X7] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X7,k3_xboole_0(X7,X6)),X6) ),
    inference(forward_demodulation,[],[f766,f146])).

fof(f766,plain,(
    ! [X6,X7] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X7,k3_xboole_0(X7,X6)),k5_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f742,f742])).

fof(f742,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(resolution,[],[f195,f133])).

fof(f133,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f63,f60])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X0,X1),X2)
      | k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(forward_demodulation,[],[f185,f84])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))
      | ~ r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f70,f42])).

fof(f70,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f51,f39,f39])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f466,plain,(
    sK1 != k5_xboole_0(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f465,f165])).

fof(f165,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3)) ),
    inference(superposition,[],[f65,f52])).

fof(f465,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f306,f454])).

fof(f454,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f295,f422])).

fof(f422,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f408,f146])).

fof(f408,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f295,f97])).

fof(f97,plain,(
    ! [X8,X7] : k1_xboole_0 = k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X8))) ),
    inference(superposition,[],[f52,f84])).

fof(f295,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(X4,X5)) = X5 ),
    inference(backward_demodulation,[],[f93,f286])).

fof(f286,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f224,f71])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(k1_xboole_0,X0) = X0 ) ),
    inference(forward_demodulation,[],[f215,f93])).

fof(f215,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f208,f42])).

fof(f208,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f60,f200])).

fof(f200,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f70,f138])).

fof(f93,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(X4,X5)) = k5_xboole_0(k1_xboole_0,X5) ),
    inference(superposition,[],[f52,f84])).

fof(f306,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f297,f52])).

fof(f297,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f61,f65])).

fof(f61,plain,(
    sK1 != k3_tarski(k4_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f31,f58,f39,f59,f59])).

fof(f31,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (13440)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (13456)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (13430)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (13445)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (13431)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (13432)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (13427)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (13435)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (13449)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (13434)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (13446)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (13448)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (13444)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (13437)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (13445)Refutation not found, incomplete strategy% (13445)------------------------------
% 0.21/0.52  % (13445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13437)Refutation not found, incomplete strategy% (13437)------------------------------
% 0.21/0.52  % (13437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13445)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13445)Memory used [KB]: 1663
% 0.21/0.52  % (13445)Time elapsed: 0.120 s
% 0.21/0.52  % (13445)------------------------------
% 0.21/0.52  % (13445)------------------------------
% 0.21/0.52  % (13456)Refutation not found, incomplete strategy% (13456)------------------------------
% 0.21/0.52  % (13456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13456)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13456)Memory used [KB]: 1663
% 0.21/0.52  % (13456)Time elapsed: 0.123 s
% 0.21/0.52  % (13456)------------------------------
% 0.21/0.52  % (13456)------------------------------
% 0.21/0.53  % (13437)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13437)Memory used [KB]: 10746
% 0.21/0.53  % (13437)Time elapsed: 0.130 s
% 0.21/0.53  % (13437)------------------------------
% 0.21/0.53  % (13437)------------------------------
% 0.21/0.53  % (13438)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (13429)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (13452)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (13454)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (13455)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (13454)Refutation not found, incomplete strategy% (13454)------------------------------
% 0.21/0.53  % (13454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13454)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13454)Memory used [KB]: 6140
% 0.21/0.53  % (13454)Time elapsed: 0.129 s
% 0.21/0.53  % (13454)------------------------------
% 0.21/0.53  % (13454)------------------------------
% 0.21/0.53  % (13455)Refutation not found, incomplete strategy% (13455)------------------------------
% 0.21/0.53  % (13455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13455)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13455)Memory used [KB]: 10746
% 0.21/0.53  % (13455)Time elapsed: 0.130 s
% 0.21/0.53  % (13455)------------------------------
% 0.21/0.53  % (13455)------------------------------
% 0.21/0.53  % (13453)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.53  % (13442)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.41/0.53  % (13441)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.41/0.53  % (13428)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.41/0.54  % (13436)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.54  % (13447)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.54  % (13439)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.41/0.54  % (13450)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.54  % (13439)Refutation not found, incomplete strategy% (13439)------------------------------
% 1.41/0.54  % (13439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (13443)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.55  % (13439)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (13439)Memory used [KB]: 10618
% 1.41/0.55  % (13439)Time elapsed: 0.152 s
% 1.41/0.55  % (13439)------------------------------
% 1.41/0.55  % (13439)------------------------------
% 1.54/0.55  % (13443)Refutation not found, incomplete strategy% (13443)------------------------------
% 1.54/0.55  % (13443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.55  % (13443)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.55  
% 1.54/0.55  % (13443)Memory used [KB]: 10618
% 1.54/0.55  % (13443)Time elapsed: 0.149 s
% 1.54/0.55  % (13443)------------------------------
% 1.54/0.55  % (13443)------------------------------
% 1.54/0.55  % (13451)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.54/0.56  % (13433)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.59  % (13449)Refutation found. Thanks to Tanya!
% 1.54/0.59  % SZS status Theorem for theBenchmark
% 1.54/0.60  % SZS output start Proof for theBenchmark
% 1.54/0.60  fof(f871,plain,(
% 1.54/0.60    $false),
% 1.54/0.60    inference(subsumption_resolution,[],[f870,f111])).
% 1.54/0.60  fof(f111,plain,(
% 1.54/0.60    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.54/0.60    inference(resolution,[],[f66,f30])).
% 1.54/0.60  fof(f30,plain,(
% 1.54/0.60    r2_hidden(sK0,sK1)),
% 1.54/0.60    inference(cnf_transformation,[],[f25])).
% 1.54/0.60  fof(f25,plain,(
% 1.54/0.60    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 1.54/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24])).
% 1.54/0.60  fof(f24,plain,(
% 1.54/0.60    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f22,plain,(
% 1.54/0.60    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 1.54/0.60    inference(ennf_transformation,[],[f21])).
% 1.54/0.60  fof(f21,negated_conjecture,(
% 1.54/0.60    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.54/0.60    inference(negated_conjecture,[],[f20])).
% 1.54/0.60  fof(f20,conjecture,(
% 1.54/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 1.54/0.60  fof(f66,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)) )),
% 1.54/0.60    inference(definition_unfolding,[],[f47,f59])).
% 1.54/0.60  fof(f59,plain,(
% 1.54/0.60    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.54/0.60    inference(definition_unfolding,[],[f34,f57])).
% 1.54/0.60  fof(f57,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.54/0.60    inference(definition_unfolding,[],[f37,f56])).
% 1.54/0.60  fof(f56,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.54/0.60    inference(definition_unfolding,[],[f50,f55])).
% 1.54/0.60  fof(f55,plain,(
% 1.54/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.54/0.60    inference(definition_unfolding,[],[f53,f54])).
% 1.54/0.60  fof(f54,plain,(
% 1.54/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f16])).
% 1.54/0.60  fof(f16,axiom,(
% 1.54/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.54/0.60  fof(f53,plain,(
% 1.54/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f15])).
% 1.54/0.60  fof(f15,axiom,(
% 1.54/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.54/0.60  fof(f50,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f14])).
% 1.54/0.60  fof(f14,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.54/0.60  fof(f37,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f13])).
% 1.54/0.60  fof(f13,axiom,(
% 1.54/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.54/0.60  fof(f34,plain,(
% 1.54/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f12])).
% 1.54/0.60  fof(f12,axiom,(
% 1.54/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.54/0.60  fof(f47,plain,(
% 1.54/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f28])).
% 1.54/0.60  fof(f28,plain,(
% 1.54/0.60    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.54/0.60    inference(nnf_transformation,[],[f17])).
% 1.54/0.60  fof(f17,axiom,(
% 1.54/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.54/0.60  fof(f870,plain,(
% 1.54/0.60    ~r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.54/0.60    inference(subsumption_resolution,[],[f866,f146])).
% 1.54/0.60  fof(f146,plain,(
% 1.54/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.60    inference(backward_demodulation,[],[f62,f143])).
% 1.54/0.60  fof(f143,plain,(
% 1.54/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f142,f84])).
% 1.54/0.60  fof(f84,plain,(
% 1.54/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f82,f71])).
% 1.54/0.60  fof(f71,plain,(
% 1.54/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.54/0.60    inference(equality_resolution,[],[f44])).
% 1.54/0.60  fof(f44,plain,(
% 1.54/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.54/0.60    inference(cnf_transformation,[],[f27])).
% 1.54/0.60  fof(f27,plain,(
% 1.54/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.60    inference(flattening,[],[f26])).
% 1.54/0.60  fof(f26,plain,(
% 1.54/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.60    inference(nnf_transformation,[],[f1])).
% 1.54/0.60  fof(f1,axiom,(
% 1.54/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.54/0.60  fof(f82,plain,(
% 1.54/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 1.54/0.60    inference(superposition,[],[f79,f42])).
% 1.54/0.60  fof(f42,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f23])).
% 1.54/0.60  fof(f23,plain,(
% 1.54/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.54/0.60    inference(ennf_transformation,[],[f4])).
% 1.54/0.60  fof(f4,axiom,(
% 1.54/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.54/0.60  fof(f79,plain,(
% 1.54/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.54/0.60    inference(resolution,[],[f68,f71])).
% 1.54/0.60  fof(f68,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.60    inference(definition_unfolding,[],[f49,f39])).
% 1.54/0.60  fof(f39,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f3])).
% 1.54/0.60  fof(f3,axiom,(
% 1.54/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.60  fof(f49,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f29])).
% 1.54/0.60  fof(f29,plain,(
% 1.54/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.54/0.60    inference(nnf_transformation,[],[f2])).
% 1.54/0.60  fof(f2,axiom,(
% 1.54/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.54/0.60  fof(f142,plain,(
% 1.54/0.60    ( ! [X1] : (k5_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f125,f138])).
% 1.54/0.60  fof(f138,plain,(
% 1.54/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.54/0.60    inference(forward_demodulation,[],[f124,f62])).
% 1.54/0.60  fof(f124,plain,(
% 1.54/0.60    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0)) )),
% 1.54/0.60    inference(superposition,[],[f60,f79])).
% 1.54/0.60  fof(f60,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.54/0.60    inference(definition_unfolding,[],[f38,f39,f39])).
% 1.54/0.60  fof(f38,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f8])).
% 1.54/0.60  fof(f8,axiom,(
% 1.54/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.54/0.60  fof(f125,plain,(
% 1.54/0.60    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k3_xboole_0(X1,X1))) )),
% 1.54/0.60    inference(superposition,[],[f60,f62])).
% 1.54/0.60  fof(f62,plain,(
% 1.54/0.60    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.54/0.60    inference(definition_unfolding,[],[f32,f39])).
% 1.54/0.60  fof(f32,plain,(
% 1.54/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.60    inference(cnf_transformation,[],[f7])).
% 1.54/0.60  fof(f7,axiom,(
% 1.54/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.54/0.60  fof(f866,plain,(
% 1.54/0.60    sK1 != k5_xboole_0(sK1,k1_xboole_0) | ~r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.54/0.60    inference(superposition,[],[f795,f275])).
% 1.54/0.60  fof(f275,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) = X2 | ~r1_tarski(X1,X2)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f274,f146])).
% 1.54/0.60  fof(f274,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k5_xboole_0(X2,k1_xboole_0) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) | ~r1_tarski(X1,X2)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f273,f143])).
% 1.54/0.60  fof(f273,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) | ~r1_tarski(X1,X2)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f272,f145])).
% 1.54/0.60  fof(f145,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 1.54/0.60    inference(backward_demodulation,[],[f91,f143])).
% 1.54/0.60  fof(f91,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1))) )),
% 1.54/0.60    inference(superposition,[],[f52,f62])).
% 1.54/0.60  fof(f52,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f10])).
% 1.54/0.60  fof(f10,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.54/0.60  fof(f272,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0))) | ~r1_tarski(X1,X2)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f271,f52])).
% 1.54/0.60  fof(f271,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) = k5_xboole_0(k5_xboole_0(X2,k1_xboole_0),k3_xboole_0(X2,k1_xboole_0)) | ~r1_tarski(X1,X2)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f270,f65])).
% 1.54/0.60  fof(f65,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.54/0.60    inference(definition_unfolding,[],[f41,f58])).
% 1.54/0.60  fof(f58,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.54/0.60    inference(definition_unfolding,[],[f36,f57])).
% 1.54/0.60  fof(f36,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f18])).
% 1.54/0.60  fof(f18,axiom,(
% 1.54/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.54/0.60  fof(f41,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f11])).
% 1.54/0.60  fof(f11,axiom,(
% 1.54/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.54/0.60  fof(f270,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k1_xboole_0)) | ~r1_tarski(X1,X2)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f254,f84])).
% 1.54/0.60  fof(f254,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k5_xboole_0(X1,X1))) | ~r1_tarski(X1,X2)) )),
% 1.54/0.60    inference(superposition,[],[f64,f42])).
% 1.54/0.60  fof(f64,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.54/0.60    inference(definition_unfolding,[],[f40,f58,f39,f58])).
% 1.54/0.60  fof(f40,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f6])).
% 1.54/0.60  fof(f6,axiom,(
% 1.54/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.54/0.60  fof(f795,plain,(
% 1.54/0.60    sK1 != k5_xboole_0(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)),
% 1.54/0.60    inference(backward_demodulation,[],[f466,f794])).
% 1.54/0.60  fof(f794,plain,(
% 1.54/0.60    ( ! [X6,X7] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X7,k3_xboole_0(X7,X6)),X6)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f766,f146])).
% 1.54/0.60  fof(f766,plain,(
% 1.54/0.60    ( ! [X6,X7] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X7,k3_xboole_0(X7,X6)),k5_xboole_0(X6,k1_xboole_0))) )),
% 1.54/0.60    inference(superposition,[],[f742,f742])).
% 1.54/0.60  fof(f742,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.54/0.60    inference(resolution,[],[f195,f133])).
% 1.54/0.60  fof(f133,plain,(
% 1.54/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.54/0.60    inference(superposition,[],[f63,f60])).
% 1.54/0.60  fof(f63,plain,(
% 1.54/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.54/0.60    inference(definition_unfolding,[],[f35,f39])).
% 1.54/0.60  fof(f35,plain,(
% 1.54/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f5])).
% 1.54/0.60  fof(f5,axiom,(
% 1.54/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.54/0.60  fof(f195,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k3_xboole_0(X0,X1),X2) | k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 1.54/0.60    inference(forward_demodulation,[],[f185,f84])).
% 1.54/0.60  fof(f185,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) | ~r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 1.54/0.60    inference(superposition,[],[f70,f42])).
% 1.54/0.60  fof(f70,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.54/0.60    inference(definition_unfolding,[],[f51,f39,f39])).
% 1.54/0.60  fof(f51,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f9])).
% 1.54/0.60  fof(f9,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.54/0.60  fof(f466,plain,(
% 1.54/0.60    sK1 != k5_xboole_0(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.54/0.60    inference(forward_demodulation,[],[f465,f165])).
% 1.54/0.60  fof(f165,plain,(
% 1.54/0.60    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) = k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3))) )),
% 1.54/0.60    inference(superposition,[],[f65,f52])).
% 1.54/0.60  fof(f465,plain,(
% 1.54/0.60    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.54/0.60    inference(backward_demodulation,[],[f306,f454])).
% 1.54/0.60  fof(f454,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 1.54/0.60    inference(superposition,[],[f295,f422])).
% 1.54/0.60  fof(f422,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.54/0.60    inference(forward_demodulation,[],[f408,f146])).
% 1.54/0.60  fof(f408,plain,(
% 1.54/0.60    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k1_xboole_0)) )),
% 1.54/0.60    inference(superposition,[],[f295,f97])).
% 1.54/0.60  fof(f97,plain,(
% 1.54/0.60    ( ! [X8,X7] : (k1_xboole_0 = k5_xboole_0(X7,k5_xboole_0(X8,k5_xboole_0(X7,X8)))) )),
% 1.54/0.60    inference(superposition,[],[f52,f84])).
% 1.54/0.60  fof(f295,plain,(
% 1.54/0.60    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X4,X5)) = X5) )),
% 1.54/0.60    inference(backward_demodulation,[],[f93,f286])).
% 1.54/0.60  fof(f286,plain,(
% 1.54/0.60    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.54/0.60    inference(resolution,[],[f224,f71])).
% 1.54/0.60  fof(f224,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.54/0.60    inference(forward_demodulation,[],[f215,f93])).
% 1.54/0.60  fof(f215,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.60    inference(superposition,[],[f208,f42])).
% 1.54/0.60  fof(f208,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.54/0.60    inference(backward_demodulation,[],[f60,f200])).
% 1.54/0.60  fof(f200,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.54/0.60    inference(superposition,[],[f70,f138])).
% 1.54/0.60  fof(f93,plain,(
% 1.54/0.60    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X4,X5)) = k5_xboole_0(k1_xboole_0,X5)) )),
% 1.54/0.60    inference(superposition,[],[f52,f84])).
% 1.54/0.60  fof(f306,plain,(
% 1.54/0.60    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.54/0.60    inference(forward_demodulation,[],[f297,f52])).
% 1.54/0.60  fof(f297,plain,(
% 1.54/0.60    sK1 != k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.54/0.60    inference(superposition,[],[f61,f65])).
% 1.54/0.60  fof(f61,plain,(
% 1.54/0.60    sK1 != k3_tarski(k4_enumset1(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.54/0.60    inference(definition_unfolding,[],[f31,f58,f39,f59,f59])).
% 1.54/0.60  fof(f31,plain,(
% 1.54/0.60    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.54/0.60    inference(cnf_transformation,[],[f25])).
% 1.54/0.60  % SZS output end Proof for theBenchmark
% 1.54/0.60  % (13449)------------------------------
% 1.54/0.60  % (13449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.60  % (13449)Termination reason: Refutation
% 1.54/0.60  
% 1.54/0.60  % (13449)Memory used [KB]: 7036
% 1.54/0.60  % (13449)Time elapsed: 0.155 s
% 1.54/0.60  % (13449)------------------------------
% 1.54/0.60  % (13449)------------------------------
% 1.54/0.60  % (13426)Success in time 0.241 s
%------------------------------------------------------------------------------
