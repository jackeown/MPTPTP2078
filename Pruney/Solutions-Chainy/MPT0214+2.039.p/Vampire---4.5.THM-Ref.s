%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:03 EST 2020

% Result     : Theorem 2.55s
% Output     : Refutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 469 expanded)
%              Number of leaves         :   21 ( 146 expanded)
%              Depth                    :   30
%              Number of atoms          :  189 ( 590 expanded)
%              Number of equality atoms :  107 ( 477 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3167,plain,(
    $false ),
    inference(resolution,[],[f3132,f349])).

fof(f349,plain,(
    ! [X2,X0,X1] : r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X0)) ),
    inference(superposition,[],[f206,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f48,f65,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f206,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f81,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f81,plain,(
    ! [X4,X0,X1] : sP5(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3132,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f194,f3126])).

fof(f3126,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f3110,f73])).

fof(f3110,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f69,f1794])).

fof(f1794,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))
      | k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8) = k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X5) ) ),
    inference(backward_demodulation,[],[f332,f1781])).

fof(f1781,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X1)) = X0 ),
    inference(forward_demodulation,[],[f1780,f149])).

fof(f149,plain,(
    ! [X8,X7] : k5_xboole_0(X7,X8) = k5_xboole_0(X7,k5_xboole_0(X7,k5_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f136,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f136,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k5_xboole_0(k5_xboole_0(X7,X7),X8)) = k5_xboole_0(X7,X8) ),
    inference(superposition,[],[f47,f84])).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f70,f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f36,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f1780,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X1)))) = X0 ),
    inference(forward_demodulation,[],[f1733,f47])).

fof(f1733,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1))) = X0 ),
    inference(unit_resulting_resolution,[],[f1657,f861])).

fof(f861,plain,(
    ! [X6,X5] :
      ( k5_xboole_0(X6,k5_xboole_0(X5,X5)) = X6
      | ~ r1_xboole_0(X5,X5) ) ),
    inference(forward_demodulation,[],[f835,f33])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f835,plain,(
    ! [X6,X5] :
      ( k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k5_xboole_0(X5,X5))
      | ~ r1_xboole_0(X5,X5) ) ),
    inference(superposition,[],[f135,f744])).

fof(f744,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f476,f724])).

fof(f724,plain,(
    ! [X9] :
      ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,X9)
      | ~ r1_xboole_0(X9,X9) ) ),
    inference(forward_demodulation,[],[f717,f33])).

fof(f717,plain,(
    ! [X9] :
      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X9)
      | ~ r1_xboole_0(X9,X9) ) ),
    inference(duplicate_literal_removal,[],[f701])).

fof(f701,plain,(
    ! [X9] :
      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X9)
      | ~ r1_xboole_0(X9,X9)
      | ~ r1_xboole_0(X9,X9) ) ),
    inference(superposition,[],[f500,f671])).

fof(f671,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f642,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f87,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f41,f37])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f642,plain,(
    ! [X8] :
      ( r1_xboole_0(k5_xboole_0(X8,X8),k5_xboole_0(X8,X8))
      | ~ r1_xboole_0(X8,X8) ) ),
    inference(global_subsumption,[],[f108,f641])).

fof(f641,plain,(
    ! [X8] :
      ( k5_xboole_0(X8,X8) != X8
      | r1_xboole_0(k5_xboole_0(X8,X8),k5_xboole_0(X8,X8))
      | ~ r1_xboole_0(X8,X8) ) ),
    inference(forward_demodulation,[],[f640,f84])).

fof(f640,plain,(
    ! [X8] :
      ( k5_xboole_0(X8,X8) != k5_xboole_0(X8,k5_xboole_0(X8,X8))
      | r1_xboole_0(k5_xboole_0(X8,X8),k5_xboole_0(X8,X8))
      | ~ r1_xboole_0(X8,X8) ) ),
    inference(forward_demodulation,[],[f612,f47])).

fof(f612,plain,(
    ! [X8] :
      ( k5_xboole_0(X8,X8) != k5_xboole_0(k5_xboole_0(X8,X8),X8)
      | r1_xboole_0(k5_xboole_0(X8,X8),k5_xboole_0(X8,X8))
      | ~ r1_xboole_0(X8,X8) ) ),
    inference(superposition,[],[f112,f587])).

fof(f587,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X4,k5_xboole_0(X3,X3)) = k5_xboole_0(X4,X3)
      | ~ r1_xboole_0(X3,X3) ) ),
    inference(forward_demodulation,[],[f569,f135])).

fof(f569,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X4,k5_xboole_0(X3,X3)) = k5_xboole_0(X4,k5_xboole_0(k1_xboole_0,X3))
      | ~ r1_xboole_0(X3,X3) ) ),
    inference(superposition,[],[f135,f500])).

fof(f112,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,X0) != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f72,f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f108,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,X0) = X0
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f71,f37])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f500,plain,(
    ! [X2] :
      ( k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X2))
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(forward_demodulation,[],[f499,f47])).

fof(f499,plain,(
    ! [X2] :
      ( k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2)
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(forward_demodulation,[],[f467,f135])).

fof(f467,plain,(
    ! [X2] :
      ( k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_xboole_0,X2))
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(superposition,[],[f174,f108])).

fof(f174,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X2))) ),
    inference(forward_demodulation,[],[f166,f47])).

fof(f166,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2)) ),
    inference(superposition,[],[f84,f135])).

fof(f476,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(X2,X2)) ),
    inference(superposition,[],[f174,f135])).

fof(f135,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k5_xboole_0(k1_xboole_0,X6)) = k5_xboole_0(X5,X6) ),
    inference(superposition,[],[f47,f33])).

fof(f1657,plain,(
    ! [X0] : r1_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f1499,f112])).

fof(f1499,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f144,f84])).

fof(f144,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X5)))) ),
    inference(superposition,[],[f84,f47])).

fof(f332,plain,(
    ! [X6,X8,X7,X5] :
      ( k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X5) = k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)))
      | ~ r1_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)) ) ),
    inference(superposition,[],[f74,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f50,f65,f62,f66,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f66])).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f69,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f31,f68,f68])).

fof(f31,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f194,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f182,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f182,plain,(
    ~ sP5(sK0,sK1,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f32,f32,f32,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f32,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (8126)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.23/0.53  % (8125)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.53  % (8136)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.23/0.53  % (8142)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.23/0.53  % (8136)Refutation not found, incomplete strategy% (8136)------------------------------
% 1.23/0.53  % (8136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (8136)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (8136)Memory used [KB]: 10618
% 1.23/0.53  % (8136)Time elapsed: 0.059 s
% 1.23/0.53  % (8136)------------------------------
% 1.23/0.53  % (8136)------------------------------
% 1.23/0.54  % (8140)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.54  % (8128)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.23/0.54  % (8128)Refutation not found, incomplete strategy% (8128)------------------------------
% 1.23/0.54  % (8128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (8128)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (8128)Memory used [KB]: 10618
% 1.23/0.54  % (8128)Time elapsed: 0.074 s
% 1.23/0.54  % (8128)------------------------------
% 1.23/0.54  % (8128)------------------------------
% 1.23/0.54  % (8121)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.54  % (8120)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.54  % (8124)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.23/0.54  % (8122)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.55  % (8143)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.55  % (8119)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.55  % (8119)Refutation not found, incomplete strategy% (8119)------------------------------
% 1.40/0.55  % (8119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (8119)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (8119)Memory used [KB]: 1663
% 1.40/0.55  % (8119)Time elapsed: 0.131 s
% 1.40/0.55  % (8119)------------------------------
% 1.40/0.55  % (8119)------------------------------
% 1.40/0.55  % (8135)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.55  % (8144)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.55  % (8123)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.55  % (8146)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.55  % (8148)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.55  % (8134)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.56  % (8147)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.56  % (8137)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.56  % (8138)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.56  % (8139)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.56  % (8134)Refutation not found, incomplete strategy% (8134)------------------------------
% 1.40/0.56  % (8134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (8127)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.56  % (8134)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (8134)Memory used [KB]: 6140
% 1.40/0.56  % (8134)Time elapsed: 0.148 s
% 1.40/0.56  % (8134)------------------------------
% 1.40/0.56  % (8134)------------------------------
% 1.40/0.56  % (8129)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.56  % (8130)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.56  % (8129)Refutation not found, incomplete strategy% (8129)------------------------------
% 1.40/0.56  % (8129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (8129)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (8129)Memory used [KB]: 10618
% 1.40/0.56  % (8129)Time elapsed: 0.149 s
% 1.40/0.56  % (8129)------------------------------
% 1.40/0.56  % (8129)------------------------------
% 1.40/0.57  % (8141)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.40/0.57  % (8131)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.57  % (8149)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.57  % (8130)Refutation not found, incomplete strategy% (8130)------------------------------
% 1.40/0.57  % (8130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (8130)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (8130)Memory used [KB]: 10618
% 1.40/0.57  % (8130)Time elapsed: 0.148 s
% 1.40/0.57  % (8130)------------------------------
% 1.40/0.57  % (8130)------------------------------
% 1.40/0.57  % (8140)Refutation not found, incomplete strategy% (8140)------------------------------
% 1.40/0.57  % (8140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (8140)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (8140)Memory used [KB]: 1918
% 1.40/0.57  % (8140)Time elapsed: 0.151 s
% 1.40/0.57  % (8140)------------------------------
% 1.40/0.57  % (8140)------------------------------
% 1.40/0.57  % (8121)Refutation not found, incomplete strategy% (8121)------------------------------
% 1.40/0.57  % (8121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (8121)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (8121)Memory used [KB]: 11001
% 1.40/0.57  % (8121)Time elapsed: 0.158 s
% 1.40/0.57  % (8121)------------------------------
% 1.40/0.57  % (8121)------------------------------
% 1.40/0.57  % (8133)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.58  % (8132)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.60  % (8127)Refutation not found, incomplete strategy% (8127)------------------------------
% 1.40/0.60  % (8127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.60  % (8127)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.60  
% 1.40/0.60  % (8127)Memory used [KB]: 11001
% 1.40/0.60  % (8127)Time elapsed: 0.170 s
% 1.40/0.60  % (8127)------------------------------
% 1.40/0.60  % (8127)------------------------------
% 1.40/0.60  % (8123)Refutation not found, incomplete strategy% (8123)------------------------------
% 1.40/0.60  % (8123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.60  % (8123)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.60  
% 1.40/0.61  % (8123)Memory used [KB]: 6524
% 1.40/0.61  % (8123)Time elapsed: 0.172 s
% 1.40/0.61  % (8123)------------------------------
% 1.40/0.61  % (8123)------------------------------
% 1.40/0.63  % (8144)Refutation not found, incomplete strategy% (8144)------------------------------
% 1.40/0.63  % (8144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.63  % (8144)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.63  
% 1.40/0.63  % (8144)Memory used [KB]: 6908
% 1.40/0.63  % (8144)Time elapsed: 0.218 s
% 1.40/0.63  % (8144)------------------------------
% 1.40/0.63  % (8144)------------------------------
% 2.04/0.66  % (8159)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.04/0.68  % (8160)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.04/0.68  % (8120)Refutation not found, incomplete strategy% (8120)------------------------------
% 2.04/0.68  % (8120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.68  % (8120)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.68  
% 2.04/0.68  % (8120)Memory used [KB]: 6140
% 2.04/0.68  % (8120)Time elapsed: 0.244 s
% 2.04/0.68  % (8120)------------------------------
% 2.04/0.68  % (8120)------------------------------
% 2.04/0.68  % (8161)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.31/0.70  % (8165)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.31/0.70  % (8164)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.31/0.70  % (8162)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.31/0.70  % (8166)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.31/0.70  % (8163)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.31/0.73  % (8172)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.55/0.75  % (8143)Refutation found. Thanks to Tanya!
% 2.55/0.75  % SZS status Theorem for theBenchmark
% 2.55/0.75  % SZS output start Proof for theBenchmark
% 2.55/0.75  fof(f3167,plain,(
% 2.55/0.75    $false),
% 2.55/0.75    inference(resolution,[],[f3132,f349])).
% 2.55/0.75  fof(f349,plain,(
% 2.55/0.75    ( ! [X2,X0,X1] : (r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X0))) )),
% 2.55/0.75    inference(superposition,[],[f206,f73])).
% 2.55/0.75  fof(f73,plain,(
% 2.55/0.75    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X3,X2,X1)) )),
% 2.55/0.75    inference(definition_unfolding,[],[f48,f65,f65])).
% 2.55/0.75  fof(f65,plain,(
% 2.55/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.55/0.75    inference(definition_unfolding,[],[f49,f64])).
% 2.55/0.75  fof(f64,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.55/0.75    inference(definition_unfolding,[],[f59,f63])).
% 2.55/0.75  fof(f63,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.55/0.75    inference(definition_unfolding,[],[f60,f61])).
% 2.55/0.75  fof(f61,plain,(
% 2.55/0.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f20])).
% 2.55/0.75  fof(f20,axiom,(
% 2.55/0.75    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.55/0.75  fof(f60,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f19])).
% 2.55/0.75  fof(f19,axiom,(
% 2.55/0.75    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.55/0.75  fof(f59,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f18])).
% 2.55/0.75  fof(f18,axiom,(
% 2.55/0.75    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.55/0.75  fof(f49,plain,(
% 2.55/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f17])).
% 2.55/0.75  fof(f17,axiom,(
% 2.55/0.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.55/0.75  fof(f48,plain,(
% 2.55/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f12])).
% 2.55/0.75  fof(f12,axiom,(
% 2.55/0.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 2.55/0.75  fof(f206,plain,(
% 2.55/0.75    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))) )),
% 2.55/0.75    inference(unit_resulting_resolution,[],[f81,f80])).
% 2.55/0.75  fof(f80,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP5(X4,X2,X1,X0)) )),
% 2.55/0.75    inference(equality_resolution,[],[f78])).
% 2.55/0.75  fof(f78,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.55/0.75    inference(definition_unfolding,[],[f55,f66])).
% 2.55/0.75  fof(f66,plain,(
% 2.55/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.55/0.75    inference(definition_unfolding,[],[f46,f65])).
% 2.55/0.75  fof(f46,plain,(
% 2.55/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f16])).
% 2.55/0.75  fof(f16,axiom,(
% 2.55/0.75    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.55/0.75  fof(f55,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.55/0.75    inference(cnf_transformation,[],[f30])).
% 2.55/0.75  fof(f30,plain,(
% 2.55/0.75    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.55/0.75    inference(ennf_transformation,[],[f11])).
% 2.55/0.75  fof(f11,axiom,(
% 2.55/0.75    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.55/0.75  fof(f81,plain,(
% 2.55/0.75    ( ! [X4,X0,X1] : (sP5(X4,X4,X1,X0)) )),
% 2.55/0.75    inference(equality_resolution,[],[f53])).
% 2.55/0.75  fof(f53,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP5(X4,X2,X1,X0)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f30])).
% 2.55/0.75  fof(f3132,plain,(
% 2.55/0.75    ~r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1,sK1))),
% 2.55/0.75    inference(backward_demodulation,[],[f194,f3126])).
% 2.55/0.75  fof(f3126,plain,(
% 2.55/0.75    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1,sK1)),
% 2.55/0.75    inference(forward_demodulation,[],[f3110,f73])).
% 2.55/0.75  fof(f3110,plain,(
% 2.55/0.75    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)),
% 2.55/0.75    inference(unit_resulting_resolution,[],[f69,f1794])).
% 2.55/0.75  fof(f1794,plain,(
% 2.55/0.75    ( ! [X6,X8,X7,X5] : (~r1_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)) | k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8) = k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X5)) )),
% 2.55/0.75    inference(backward_demodulation,[],[f332,f1781])).
% 2.55/0.75  fof(f1781,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X1)) = X0) )),
% 2.55/0.75    inference(forward_demodulation,[],[f1780,f149])).
% 2.55/0.75  fof(f149,plain,(
% 2.55/0.75    ( ! [X8,X7] : (k5_xboole_0(X7,X8) = k5_xboole_0(X7,k5_xboole_0(X7,k5_xboole_0(X7,X8)))) )),
% 2.55/0.75    inference(forward_demodulation,[],[f136,f47])).
% 2.55/0.75  fof(f47,plain,(
% 2.55/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.55/0.75    inference(cnf_transformation,[],[f9])).
% 2.55/0.75  fof(f9,axiom,(
% 2.55/0.75    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.55/0.75  fof(f136,plain,(
% 2.55/0.75    ( ! [X8,X7] : (k5_xboole_0(X7,k5_xboole_0(k5_xboole_0(X7,X7),X8)) = k5_xboole_0(X7,X8)) )),
% 2.55/0.75    inference(superposition,[],[f47,f84])).
% 2.55/0.75  fof(f84,plain,(
% 2.55/0.75    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 2.55/0.75    inference(backward_demodulation,[],[f70,f37])).
% 2.55/0.75  fof(f37,plain,(
% 2.55/0.75    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.55/0.75    inference(cnf_transformation,[],[f24])).
% 2.55/0.75  fof(f24,plain,(
% 2.55/0.75    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.55/0.75    inference(rectify,[],[f2])).
% 2.55/0.75  fof(f2,axiom,(
% 2.55/0.75    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.55/0.75  fof(f70,plain,(
% 2.55/0.75    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.55/0.75    inference(definition_unfolding,[],[f36,f62])).
% 2.55/0.75  fof(f62,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.55/0.75    inference(definition_unfolding,[],[f39,f40])).
% 2.55/0.75  fof(f40,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.55/0.75    inference(cnf_transformation,[],[f5])).
% 2.55/0.75  fof(f5,axiom,(
% 2.55/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.55/0.75  fof(f39,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.55/0.75    inference(cnf_transformation,[],[f10])).
% 2.55/0.75  fof(f10,axiom,(
% 2.55/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.55/0.75  fof(f36,plain,(
% 2.55/0.75    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.55/0.75    inference(cnf_transformation,[],[f23])).
% 2.55/0.75  fof(f23,plain,(
% 2.55/0.75    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.55/0.75    inference(rectify,[],[f1])).
% 2.55/0.75  fof(f1,axiom,(
% 2.55/0.75    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.55/0.75  fof(f1780,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X1)))) = X0) )),
% 2.55/0.75    inference(forward_demodulation,[],[f1733,f47])).
% 2.55/0.75  fof(f1733,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1))) = X0) )),
% 2.55/0.75    inference(unit_resulting_resolution,[],[f1657,f861])).
% 2.55/0.75  fof(f861,plain,(
% 2.55/0.75    ( ! [X6,X5] : (k5_xboole_0(X6,k5_xboole_0(X5,X5)) = X6 | ~r1_xboole_0(X5,X5)) )),
% 2.55/0.75    inference(forward_demodulation,[],[f835,f33])).
% 2.55/0.75  fof(f33,plain,(
% 2.55/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.55/0.75    inference(cnf_transformation,[],[f7])).
% 2.55/0.75  fof(f7,axiom,(
% 2.55/0.75    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.55/0.75  fof(f835,plain,(
% 2.55/0.75    ( ! [X6,X5] : (k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k5_xboole_0(X5,X5)) | ~r1_xboole_0(X5,X5)) )),
% 2.55/0.75    inference(superposition,[],[f135,f744])).
% 2.55/0.75  fof(f744,plain,(
% 2.55/0.75    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)) | ~r1_xboole_0(X0,X0)) )),
% 2.55/0.75    inference(superposition,[],[f476,f724])).
% 2.55/0.75  fof(f724,plain,(
% 2.55/0.75    ( ! [X9] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,X9) | ~r1_xboole_0(X9,X9)) )),
% 2.55/0.75    inference(forward_demodulation,[],[f717,f33])).
% 2.55/0.75  fof(f717,plain,(
% 2.55/0.75    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X9) | ~r1_xboole_0(X9,X9)) )),
% 2.55/0.75    inference(duplicate_literal_removal,[],[f701])).
% 2.55/0.75  fof(f701,plain,(
% 2.55/0.75    ( ! [X9] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X9) | ~r1_xboole_0(X9,X9) | ~r1_xboole_0(X9,X9)) )),
% 2.55/0.75    inference(superposition,[],[f500,f671])).
% 2.55/0.75  fof(f671,plain,(
% 2.55/0.75    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_xboole_0(X0,X0)) )),
% 2.55/0.75    inference(resolution,[],[f642,f89])).
% 2.55/0.75  fof(f89,plain,(
% 2.55/0.75    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.55/0.75    inference(resolution,[],[f87,f35])).
% 2.55/0.75  fof(f35,plain,(
% 2.55/0.75    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.55/0.75    inference(cnf_transformation,[],[f27])).
% 2.55/0.75  fof(f27,plain,(
% 2.55/0.75    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.55/0.75    inference(ennf_transformation,[],[f4])).
% 2.55/0.75  fof(f4,axiom,(
% 2.55/0.75    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.55/0.75  fof(f87,plain,(
% 2.55/0.75    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 2.55/0.75    inference(superposition,[],[f41,f37])).
% 2.55/0.75  fof(f41,plain,(
% 2.55/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f28])).
% 2.55/0.75  fof(f28,plain,(
% 2.55/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.55/0.75    inference(ennf_transformation,[],[f25])).
% 2.55/0.75  fof(f25,plain,(
% 2.55/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.55/0.75    inference(rectify,[],[f3])).
% 2.55/0.75  fof(f3,axiom,(
% 2.55/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.55/0.75  fof(f642,plain,(
% 2.55/0.75    ( ! [X8] : (r1_xboole_0(k5_xboole_0(X8,X8),k5_xboole_0(X8,X8)) | ~r1_xboole_0(X8,X8)) )),
% 2.55/0.75    inference(global_subsumption,[],[f108,f641])).
% 2.55/0.75  fof(f641,plain,(
% 2.55/0.75    ( ! [X8] : (k5_xboole_0(X8,X8) != X8 | r1_xboole_0(k5_xboole_0(X8,X8),k5_xboole_0(X8,X8)) | ~r1_xboole_0(X8,X8)) )),
% 2.55/0.75    inference(forward_demodulation,[],[f640,f84])).
% 2.55/0.75  fof(f640,plain,(
% 2.55/0.75    ( ! [X8] : (k5_xboole_0(X8,X8) != k5_xboole_0(X8,k5_xboole_0(X8,X8)) | r1_xboole_0(k5_xboole_0(X8,X8),k5_xboole_0(X8,X8)) | ~r1_xboole_0(X8,X8)) )),
% 2.55/0.75    inference(forward_demodulation,[],[f612,f47])).
% 2.55/0.75  fof(f612,plain,(
% 2.55/0.75    ( ! [X8] : (k5_xboole_0(X8,X8) != k5_xboole_0(k5_xboole_0(X8,X8),X8) | r1_xboole_0(k5_xboole_0(X8,X8),k5_xboole_0(X8,X8)) | ~r1_xboole_0(X8,X8)) )),
% 2.55/0.75    inference(superposition,[],[f112,f587])).
% 2.55/0.75  fof(f587,plain,(
% 2.55/0.75    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X3)) = k5_xboole_0(X4,X3) | ~r1_xboole_0(X3,X3)) )),
% 2.55/0.75    inference(forward_demodulation,[],[f569,f135])).
% 2.55/0.75  fof(f569,plain,(
% 2.55/0.75    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X3)) = k5_xboole_0(X4,k5_xboole_0(k1_xboole_0,X3)) | ~r1_xboole_0(X3,X3)) )),
% 2.55/0.75    inference(superposition,[],[f135,f500])).
% 2.55/0.75  fof(f112,plain,(
% 2.55/0.75    ( ! [X0] : (k5_xboole_0(X0,X0) != X0 | r1_xboole_0(X0,X0)) )),
% 2.55/0.75    inference(superposition,[],[f72,f37])).
% 2.55/0.75  fof(f72,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 2.55/0.75    inference(definition_unfolding,[],[f44,f40])).
% 2.55/0.75  fof(f44,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f8])).
% 2.55/0.75  fof(f8,axiom,(
% 2.55/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.55/0.75  fof(f108,plain,(
% 2.55/0.75    ( ! [X0] : (k5_xboole_0(X0,X0) = X0 | ~r1_xboole_0(X0,X0)) )),
% 2.55/0.75    inference(superposition,[],[f71,f37])).
% 2.55/0.75  fof(f71,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.55/0.75    inference(definition_unfolding,[],[f45,f40])).
% 2.55/0.75  fof(f45,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f8])).
% 2.55/0.75  fof(f500,plain,(
% 2.55/0.75    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X2)) | ~r1_xboole_0(X2,X2)) )),
% 2.55/0.75    inference(forward_demodulation,[],[f499,f47])).
% 2.55/0.75  fof(f499,plain,(
% 2.55/0.75    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2) | ~r1_xboole_0(X2,X2)) )),
% 2.55/0.75    inference(forward_demodulation,[],[f467,f135])).
% 2.55/0.75  fof(f467,plain,(
% 2.55/0.75    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_xboole_0,X2)) | ~r1_xboole_0(X2,X2)) )),
% 2.55/0.75    inference(superposition,[],[f174,f108])).
% 2.55/0.75  fof(f174,plain,(
% 2.55/0.75    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,X2)))) )),
% 2.55/0.75    inference(forward_demodulation,[],[f166,f47])).
% 2.55/0.75  fof(f166,plain,(
% 2.55/0.75    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2))) )),
% 2.55/0.75    inference(superposition,[],[f84,f135])).
% 2.55/0.75  fof(f476,plain,(
% 2.55/0.75    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(X2,X2))) )),
% 2.55/0.75    inference(superposition,[],[f174,f135])).
% 2.55/0.75  fof(f135,plain,(
% 2.55/0.75    ( ! [X6,X5] : (k5_xboole_0(X5,k5_xboole_0(k1_xboole_0,X6)) = k5_xboole_0(X5,X6)) )),
% 2.55/0.75    inference(superposition,[],[f47,f33])).
% 2.55/0.75  fof(f1657,plain,(
% 2.55/0.75    ( ! [X0] : (r1_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) )),
% 2.55/0.75    inference(unit_resulting_resolution,[],[f1499,f112])).
% 2.55/0.75  fof(f1499,plain,(
% 2.55/0.75    ( ! [X0] : (k5_xboole_0(X0,X0) = k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))) )),
% 2.55/0.75    inference(superposition,[],[f144,f84])).
% 2.55/0.75  fof(f144,plain,(
% 2.55/0.75    ( ! [X4,X5] : (k5_xboole_0(X4,X5) = k5_xboole_0(k5_xboole_0(X4,X5),k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,X5))))) )),
% 2.55/0.75    inference(superposition,[],[f84,f47])).
% 2.55/0.75  fof(f332,plain,(
% 2.55/0.75    ( ! [X6,X8,X7,X5] : (k6_enumset1(X6,X6,X6,X6,X6,X7,X8,X5) = k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8),k5_xboole_0(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))) | ~r1_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) )),
% 2.55/0.75    inference(superposition,[],[f74,f43])).
% 2.55/0.75  fof(f43,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f29])).
% 2.55/0.75  fof(f29,plain,(
% 2.55/0.75    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.55/0.75    inference(ennf_transformation,[],[f6])).
% 2.55/0.75  fof(f6,axiom,(
% 2.55/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.55/0.75  fof(f74,plain,(
% 2.55/0.75    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))))) )),
% 2.55/0.75    inference(definition_unfolding,[],[f50,f65,f62,f66,f68])).
% 2.55/0.75  fof(f68,plain,(
% 2.55/0.75    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.55/0.75    inference(definition_unfolding,[],[f34,f67])).
% 2.55/0.75  fof(f67,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.55/0.75    inference(definition_unfolding,[],[f38,f66])).
% 2.55/0.75  fof(f38,plain,(
% 2.55/0.75    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f15])).
% 2.55/0.75  fof(f15,axiom,(
% 2.55/0.75    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.55/0.75  fof(f34,plain,(
% 2.55/0.75    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.55/0.75    inference(cnf_transformation,[],[f14])).
% 2.55/0.75  fof(f14,axiom,(
% 2.55/0.75    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.55/0.75  fof(f50,plain,(
% 2.55/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.55/0.75    inference(cnf_transformation,[],[f13])).
% 2.55/0.75  fof(f13,axiom,(
% 2.55/0.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 2.55/0.75  fof(f69,plain,(
% 2.55/0.75    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.55/0.75    inference(definition_unfolding,[],[f31,f68,f68])).
% 2.55/0.75  fof(f31,plain,(
% 2.55/0.75    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 2.55/0.75    inference(cnf_transformation,[],[f26])).
% 2.55/0.75  fof(f26,plain,(
% 2.55/0.75    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.55/0.75    inference(ennf_transformation,[],[f22])).
% 2.55/0.75  fof(f22,negated_conjecture,(
% 2.55/0.75    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.55/0.75    inference(negated_conjecture,[],[f21])).
% 2.55/0.75  fof(f21,conjecture,(
% 2.55/0.75    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.55/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 2.55/0.75  fof(f194,plain,(
% 2.55/0.75    ~r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.55/0.75    inference(unit_resulting_resolution,[],[f182,f79])).
% 2.55/0.75  fof(f79,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | sP5(X4,X2,X1,X0)) )),
% 2.55/0.75    inference(equality_resolution,[],[f77])).
% 2.55/0.75  fof(f77,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.55/0.75    inference(definition_unfolding,[],[f56,f66])).
% 2.55/0.75  fof(f56,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.55/0.75    inference(cnf_transformation,[],[f30])).
% 2.55/0.75  fof(f182,plain,(
% 2.55/0.75    ~sP5(sK0,sK1,sK1,sK1)),
% 2.55/0.75    inference(unit_resulting_resolution,[],[f32,f32,f32,f54])).
% 2.55/0.75  fof(f54,plain,(
% 2.55/0.75    ( ! [X4,X2,X0,X1] : (~sP5(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 2.55/0.75    inference(cnf_transformation,[],[f30])).
% 2.55/0.75  fof(f32,plain,(
% 2.55/0.75    sK0 != sK1),
% 2.55/0.75    inference(cnf_transformation,[],[f26])).
% 2.55/0.75  % SZS output end Proof for theBenchmark
% 2.55/0.75  % (8143)------------------------------
% 2.55/0.75  % (8143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.75  % (8143)Termination reason: Refutation
% 2.55/0.75  
% 2.55/0.75  % (8143)Memory used [KB]: 7931
% 2.55/0.75  % (8143)Time elapsed: 0.340 s
% 2.55/0.75  % (8143)------------------------------
% 2.55/0.75  % (8143)------------------------------
% 2.55/0.76  % (8117)Success in time 0.383 s
%------------------------------------------------------------------------------
