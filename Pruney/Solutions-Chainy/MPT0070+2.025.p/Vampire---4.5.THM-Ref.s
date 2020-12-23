%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:29 EST 2020

% Result     : Theorem 7.14s
% Output     : Refutation 7.14s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 450 expanded)
%              Number of leaves         :   11 ( 139 expanded)
%              Depth                    :   34
%              Number of atoms          :  141 ( 699 expanded)
%              Number of equality atoms :   80 ( 384 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48449,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48445,f20])).

fof(f20,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f48445,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f48387])).

fof(f48387,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f363,f48363])).

fof(f48363,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f48330,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f48330,plain,(
    r1_tarski(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f47794,f387])).

fof(f387,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f386,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f386,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))) = k4_xboole_0(X10,k2_xboole_0(X11,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f354,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f354,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))) = k4_xboole_0(k4_xboole_0(X10,X11),k1_xboole_0) ),
    inference(superposition,[],[f32,f39])).

fof(f39,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(resolution,[],[f30,f23])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47794,plain,(
    ! [X67] : r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(X67,k4_xboole_0(X67,sK0)))) ),
    inference(superposition,[],[f47716,f32])).

fof(f47716,plain,(
    ! [X25] : r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,X25))) ),
    inference(trivial_inequality_removal,[],[f47672])).

fof(f47672,plain,(
    ! [X25] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,X25))) ) ),
    inference(superposition,[],[f29,f47297])).

fof(f47297,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,X0))) ),
    inference(resolution,[],[f47289,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f47289,plain,(
    ! [X9] : r1_xboole_0(sK2,k4_xboole_0(sK0,X9)) ),
    inference(forward_demodulation,[],[f47288,f21])).

fof(f47288,plain,(
    ! [X9] : r1_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(X9,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f47245,f31])).

fof(f47245,plain,(
    ! [X9] : r1_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK0,X9),k1_xboole_0)) ),
    inference(superposition,[],[f46812,f19533])).

fof(f19533,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(resolution,[],[f19487,f30])).

fof(f19487,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(sK0,X1),k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f19420,f10733])).

fof(f10733,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),sK1) ),
    inference(backward_demodulation,[],[f121,f10569])).

fof(f10569,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f10568,f109])).

fof(f109,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f34,f19])).

fof(f19,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f10568,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f10567,f21])).

fof(f10567,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK1,k2_xboole_0(sK2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f10566,f31])).

fof(f10566,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f10565,f21])).

fof(f10565,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f10564,f21])).

fof(f10564,plain,(
    k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f10563,f31])).

fof(f10563,plain,(
    k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f10238,f31])).

fof(f10238,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f355,f6480])).

fof(f6480,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[],[f148,f6445])).

fof(f6445,plain,(
    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f6444,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f6444,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f6074,f39])).

fof(f6074,plain,(
    k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f365,f109])).

fof(f365,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),X4) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f26,f32])).

fof(f148,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f31,f39])).

fof(f355,plain,(
    ! [X14,X12,X13] : k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X12,X13))) = k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k2_xboole_0(X13,X14))) ),
    inference(superposition,[],[f32,f31])).

fof(f121,plain,(
    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f115,f21])).

fof(f115,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f26,f109])).

fof(f19420,plain,(
    ! [X90,X89] : r1_tarski(k4_xboole_0(sK0,X89),k2_xboole_0(X90,sK1)) ),
    inference(trivial_inequality_removal,[],[f19366])).

fof(f19366,plain,(
    ! [X90,X89] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(sK0,X89),k2_xboole_0(X90,sK1)) ) ),
    inference(superposition,[],[f155,f17685])).

fof(f17685,plain,(
    ! [X17,X18] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X17,k2_xboole_0(X18,sK1))) ),
    inference(superposition,[],[f17499,f169])).

fof(f169,plain,(
    ! [X14,X12,X13,X11] : k4_xboole_0(X11,k2_xboole_0(k2_xboole_0(X12,X13),X14)) = k4_xboole_0(X11,k2_xboole_0(X12,k2_xboole_0(X13,X14))) ),
    inference(forward_demodulation,[],[f168,f31])).

fof(f168,plain,(
    ! [X14,X12,X13,X11] : k4_xboole_0(k4_xboole_0(X11,X12),k2_xboole_0(X13,X14)) = k4_xboole_0(X11,k2_xboole_0(k2_xboole_0(X12,X13),X14)) ),
    inference(forward_demodulation,[],[f145,f31])).

fof(f145,plain,(
    ! [X14,X12,X13,X11] : k4_xboole_0(k4_xboole_0(X11,X12),k2_xboole_0(X13,X14)) = k4_xboole_0(k4_xboole_0(X11,k2_xboole_0(X12,X13)),X14) ),
    inference(superposition,[],[f31,f31])).

fof(f17499,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,sK1)) ),
    inference(superposition,[],[f17344,f31])).

fof(f17344,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X4),sK1) ),
    inference(superposition,[],[f5082,f148])).

fof(f5082,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k2_xboole_0(sK1,k4_xboole_0(sK0,X6))) = k4_xboole_0(X7,sK1) ),
    inference(forward_demodulation,[],[f5043,f76])).

fof(f76,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f70,f21])).

fof(f70,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f26,f36])).

fof(f36,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f5043,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k2_xboole_0(sK1,k4_xboole_0(sK0,X6))) = k4_xboole_0(X7,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f4902,f75])).

fof(f75,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f69,f21])).

fof(f69,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X4,X5)) = k2_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f26,f39])).

fof(f4902,plain,(
    ! [X64,X63] : k4_xboole_0(X63,k2_xboole_0(sK1,k2_xboole_0(sK0,X64))) = k4_xboole_0(X63,k2_xboole_0(sK1,X64)) ),
    inference(superposition,[],[f169,f76])).

fof(f155,plain,(
    ! [X12,X10,X11] :
      ( k1_xboole_0 != k4_xboole_0(X10,k2_xboole_0(X11,X12))
      | r1_tarski(k4_xboole_0(X10,X11),X12) ) ),
    inference(superposition,[],[f29,f31])).

fof(f46812,plain,(
    ! [X1] : r1_xboole_0(sK2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,k1_xboole_0)))) ),
    inference(superposition,[],[f46640,f388])).

fof(f388,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X5,X6))) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ),
    inference(forward_demodulation,[],[f357,f31])).

fof(f357,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X7))) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f32,f31])).

fof(f46640,plain,(
    ! [X47] : r1_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X47))) ),
    inference(superposition,[],[f34835,f10807])).

fof(f10807,plain,(
    ! [X1] : k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(forward_demodulation,[],[f10786,f31])).

fof(f10786,plain,(
    ! [X1] : k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X1) ),
    inference(superposition,[],[f31,f10569])).

fof(f34835,plain,(
    ! [X30,X28,X29] : r1_xboole_0(X28,k4_xboole_0(X30,k2_xboole_0(X28,X29))) ),
    inference(superposition,[],[f26769,f74])).

fof(f74,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f68,f21])).

fof(f68,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[],[f26,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f30,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f26769,plain,(
    ! [X39,X41,X40] : r1_xboole_0(X41,k4_xboole_0(X39,k2_xboole_0(X40,X41))) ),
    inference(superposition,[],[f26661,f31])).

fof(f26661,plain,(
    ! [X14,X15] : r1_xboole_0(X14,k4_xboole_0(X15,X14)) ),
    inference(trivial_inequality_removal,[],[f26574])).

fof(f26574,plain,(
    ! [X14,X15] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X14,k4_xboole_0(X15,X14)) ) ),
    inference(superposition,[],[f33,f12317])).

fof(f12317,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f12316,f148])).

fof(f12316,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f11833,f26])).

fof(f11833,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f388,f154])).

fof(f154,plain,(
    ! [X8,X7,X9] : k2_xboole_0(X9,k4_xboole_0(X7,X8)) = k2_xboole_0(X9,k4_xboole_0(X7,k2_xboole_0(X8,X9))) ),
    inference(superposition,[],[f26,f31])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f363,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,k4_xboole_0(X1,X0))
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f33,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (21356)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.43  % (21354)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (21350)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (21351)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (21353)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (21365)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (21362)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (21364)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (21357)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (21359)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (21360)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (21358)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (21355)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (21363)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (21348)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (21349)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.53  % (21367)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (21366)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 5.40/1.04  % (21353)Time limit reached!
% 5.40/1.04  % (21353)------------------------------
% 5.40/1.04  % (21353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.05  % (21353)Termination reason: Time limit
% 5.40/1.05  % (21353)Termination phase: Saturation
% 5.40/1.05  
% 5.40/1.05  % (21353)Memory used [KB]: 15351
% 5.40/1.05  % (21353)Time elapsed: 0.600 s
% 5.40/1.05  % (21353)------------------------------
% 5.40/1.05  % (21353)------------------------------
% 7.14/1.29  % (21362)Refutation found. Thanks to Tanya!
% 7.14/1.29  % SZS status Theorem for theBenchmark
% 7.14/1.29  % SZS output start Proof for theBenchmark
% 7.14/1.29  fof(f48449,plain,(
% 7.14/1.29    $false),
% 7.14/1.29    inference(subsumption_resolution,[],[f48445,f20])).
% 7.14/1.29  fof(f20,plain,(
% 7.14/1.29    ~r1_xboole_0(sK0,sK2)),
% 7.14/1.29    inference(cnf_transformation,[],[f15])).
% 7.14/1.29  fof(f15,plain,(
% 7.14/1.29    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 7.14/1.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 7.14/1.29  fof(f14,plain,(
% 7.14/1.29    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 7.14/1.29    introduced(choice_axiom,[])).
% 7.14/1.29  fof(f13,plain,(
% 7.14/1.29    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 7.14/1.29    inference(flattening,[],[f12])).
% 7.14/1.29  fof(f12,plain,(
% 7.14/1.29    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 7.14/1.29    inference(ennf_transformation,[],[f11])).
% 7.14/1.29  fof(f11,negated_conjecture,(
% 7.14/1.29    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 7.14/1.29    inference(negated_conjecture,[],[f10])).
% 7.14/1.29  fof(f10,conjecture,(
% 7.14/1.29    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 7.14/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 7.14/1.29  fof(f48445,plain,(
% 7.14/1.29    r1_xboole_0(sK0,sK2)),
% 7.14/1.29    inference(trivial_inequality_removal,[],[f48387])).
% 7.14/1.29  fof(f48387,plain,(
% 7.14/1.29    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK2)),
% 7.14/1.29    inference(superposition,[],[f363,f48363])).
% 7.14/1.29  fof(f48363,plain,(
% 7.14/1.29    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 7.14/1.29    inference(resolution,[],[f48330,f30])).
% 7.14/1.29  fof(f30,plain,(
% 7.14/1.29    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 7.14/1.29    inference(cnf_transformation,[],[f17])).
% 7.14/1.29  fof(f17,plain,(
% 7.14/1.29    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.14/1.29    inference(nnf_transformation,[],[f3])).
% 7.14/1.29  fof(f3,axiom,(
% 7.14/1.29    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.14/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 7.14/1.29  fof(f48330,plain,(
% 7.14/1.29    r1_tarski(sK2,k4_xboole_0(sK2,sK0))),
% 7.14/1.29    inference(superposition,[],[f47794,f387])).
% 7.14/1.29  fof(f387,plain,(
% 7.14/1.29    ( ! [X10,X11] : (k4_xboole_0(X10,X11) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 7.14/1.29    inference(forward_demodulation,[],[f386,f21])).
% 7.14/1.29  fof(f21,plain,(
% 7.14/1.29    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.14/1.29    inference(cnf_transformation,[],[f4])).
% 7.14/1.29  fof(f4,axiom,(
% 7.14/1.29    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.14/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 7.14/1.29  fof(f386,plain,(
% 7.14/1.29    ( ! [X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))) = k4_xboole_0(X10,k2_xboole_0(X11,k1_xboole_0))) )),
% 7.14/1.29    inference(forward_demodulation,[],[f354,f31])).
% 7.14/1.29  fof(f31,plain,(
% 7.14/1.29    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.14/1.29    inference(cnf_transformation,[],[f7])).
% 7.14/1.29  fof(f7,axiom,(
% 7.14/1.29    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 7.14/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 7.14/1.29  fof(f354,plain,(
% 7.14/1.29    ( ! [X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))) = k4_xboole_0(k4_xboole_0(X10,X11),k1_xboole_0)) )),
% 7.14/1.29    inference(superposition,[],[f32,f39])).
% 7.14/1.29  fof(f39,plain,(
% 7.14/1.29    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 7.14/1.29    inference(resolution,[],[f30,f23])).
% 7.14/1.29  fof(f23,plain,(
% 7.14/1.29    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.14/1.29    inference(cnf_transformation,[],[f5])).
% 7.14/1.29  fof(f5,axiom,(
% 7.14/1.29    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.14/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 7.14/1.29  fof(f32,plain,(
% 7.14/1.29    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.14/1.29    inference(definition_unfolding,[],[f24,f25,f25])).
% 7.14/1.29  fof(f25,plain,(
% 7.14/1.29    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.14/1.29    inference(cnf_transformation,[],[f8])).
% 7.14/1.29  fof(f8,axiom,(
% 7.14/1.29    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.14/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 7.14/1.29  fof(f24,plain,(
% 7.14/1.29    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.14/1.29    inference(cnf_transformation,[],[f1])).
% 7.14/1.29  fof(f1,axiom,(
% 7.14/1.29    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.14/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.14/1.29  fof(f47794,plain,(
% 7.14/1.29    ( ! [X67] : (r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(X67,k4_xboole_0(X67,sK0))))) )),
% 7.14/1.29    inference(superposition,[],[f47716,f32])).
% 7.14/1.29  fof(f47716,plain,(
% 7.14/1.29    ( ! [X25] : (r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,X25)))) )),
% 7.14/1.29    inference(trivial_inequality_removal,[],[f47672])).
% 7.14/1.29  fof(f47672,plain,(
% 7.14/1.29    ( ! [X25] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,X25)))) )),
% 7.14/1.29    inference(superposition,[],[f29,f47297])).
% 7.14/1.29  fof(f47297,plain,(
% 7.14/1.29    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,X0)))) )),
% 7.14/1.29    inference(resolution,[],[f47289,f34])).
% 7.14/1.29  fof(f34,plain,(
% 7.14/1.29    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.14/1.29    inference(definition_unfolding,[],[f27,f25])).
% 7.14/1.29  fof(f27,plain,(
% 7.14/1.29    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.14/1.29    inference(cnf_transformation,[],[f16])).
% 7.14/1.29  fof(f16,plain,(
% 7.14/1.29    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.14/1.29    inference(nnf_transformation,[],[f2])).
% 7.14/1.29  fof(f2,axiom,(
% 7.14/1.29    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.14/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 7.14/1.29  fof(f47289,plain,(
% 7.14/1.29    ( ! [X9] : (r1_xboole_0(sK2,k4_xboole_0(sK0,X9))) )),
% 7.14/1.29    inference(forward_demodulation,[],[f47288,f21])).
% 7.14/1.29  fof(f47288,plain,(
% 7.14/1.29    ( ! [X9] : (r1_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(X9,k1_xboole_0)))) )),
% 7.14/1.29    inference(forward_demodulation,[],[f47245,f31])).
% 7.14/1.29  fof(f47245,plain,(
% 7.14/1.29    ( ! [X9] : (r1_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK0,X9),k1_xboole_0))) )),
% 7.14/1.29    inference(superposition,[],[f46812,f19533])).
% 7.14/1.29  fof(f19533,plain,(
% 7.14/1.29    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,k1_xboole_0))) )),
% 7.14/1.29    inference(resolution,[],[f19487,f30])).
% 7.14/1.29  fof(f19487,plain,(
% 7.14/1.29    ( ! [X1] : (r1_tarski(k4_xboole_0(sK0,X1),k4_xboole_0(sK1,k1_xboole_0))) )),
% 7.14/1.29    inference(superposition,[],[f19420,f10733])).
% 7.14/1.29  fof(f10733,plain,(
% 7.14/1.29    k4_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),sK1)),
% 7.14/1.29    inference(backward_demodulation,[],[f121,f10569])).
% 7.14/1.29  fof(f10569,plain,(
% 7.14/1.29    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)),
% 7.14/1.29    inference(forward_demodulation,[],[f10568,f109])).
% 7.14/1.29  fof(f109,plain,(
% 7.14/1.29    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 7.14/1.29    inference(resolution,[],[f34,f19])).
% 7.14/1.29  fof(f19,plain,(
% 7.14/1.29    r1_xboole_0(sK1,sK2)),
% 7.14/1.29    inference(cnf_transformation,[],[f15])).
% 7.14/1.29  fof(f10568,plain,(
% 7.14/1.29    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 7.14/1.29    inference(forward_demodulation,[],[f10567,f21])).
% 7.14/1.29  fof(f10567,plain,(
% 7.14/1.29    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK1,k2_xboole_0(sK2,k1_xboole_0))),
% 7.14/1.29    inference(forward_demodulation,[],[f10566,f31])).
% 7.14/1.29  fof(f10566,plain,(
% 7.14/1.29    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 7.14/1.29    inference(forward_demodulation,[],[f10565,f21])).
% 7.14/1.29  fof(f10565,plain,(
% 7.14/1.29    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k1_xboole_0))),
% 7.14/1.29    inference(forward_demodulation,[],[f10564,f21])).
% 7.14/1.29  fof(f10564,plain,(
% 7.14/1.29    k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,k1_xboole_0))))),
% 7.14/1.29    inference(forward_demodulation,[],[f10563,f31])).
% 7.14/1.29  fof(f10563,plain,(
% 7.14/1.29    k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)))),
% 7.14/1.29    inference(forward_demodulation,[],[f10238,f31])).
% 7.14/1.29  fof(f10238,plain,(
% 7.14/1.29    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),k1_xboole_0)),
% 7.14/1.29    inference(superposition,[],[f355,f6480])).
% 7.14/1.29  fof(f6480,plain,(
% 7.14/1.29    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,sK1))),
% 7.14/1.29    inference(superposition,[],[f148,f6445])).
% 7.14/1.29  fof(f6445,plain,(
% 7.14/1.29    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),
% 7.14/1.29    inference(forward_demodulation,[],[f6444,f26])).
% 7.14/1.29  fof(f26,plain,(
% 7.14/1.29    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.14/1.29    inference(cnf_transformation,[],[f6])).
% 7.14/1.29  fof(f6,axiom,(
% 7.14/1.29    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.14/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 7.14/1.29  fof(f6444,plain,(
% 7.14/1.29    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_xboole_0))),
% 7.14/1.29    inference(forward_demodulation,[],[f6074,f39])).
% 7.14/1.29  fof(f6074,plain,(
% 7.14/1.29    k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),sK1),k4_xboole_0(sK1,k1_xboole_0))),
% 7.14/1.29    inference(superposition,[],[f365,f109])).
% 7.14/1.29  fof(f365,plain,(
% 7.14/1.29    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),X4) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4)))) )),
% 7.14/1.29    inference(superposition,[],[f26,f32])).
% 7.14/1.29  fof(f148,plain,(
% 7.14/1.29    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 7.14/1.29    inference(superposition,[],[f31,f39])).
% 7.14/1.29  fof(f355,plain,(
% 7.14/1.29    ( ! [X14,X12,X13] : (k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X12,X13))) = k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,k2_xboole_0(X13,X14)))) )),
% 7.14/1.29    inference(superposition,[],[f32,f31])).
% 7.14/1.29  fof(f121,plain,(
% 7.14/1.29    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)),
% 7.14/1.29    inference(forward_demodulation,[],[f115,f21])).
% 7.14/1.29  fof(f115,plain,(
% 7.14/1.29    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 7.14/1.29    inference(superposition,[],[f26,f109])).
% 7.14/1.29  fof(f19420,plain,(
% 7.14/1.29    ( ! [X90,X89] : (r1_tarski(k4_xboole_0(sK0,X89),k2_xboole_0(X90,sK1))) )),
% 7.14/1.29    inference(trivial_inequality_removal,[],[f19366])).
% 7.14/1.29  fof(f19366,plain,(
% 7.14/1.29    ( ! [X90,X89] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,X89),k2_xboole_0(X90,sK1))) )),
% 7.14/1.29    inference(superposition,[],[f155,f17685])).
% 7.14/1.29  fof(f17685,plain,(
% 7.14/1.29    ( ! [X17,X18] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X17,k2_xboole_0(X18,sK1)))) )),
% 7.14/1.29    inference(superposition,[],[f17499,f169])).
% 7.14/1.29  fof(f169,plain,(
% 7.14/1.29    ( ! [X14,X12,X13,X11] : (k4_xboole_0(X11,k2_xboole_0(k2_xboole_0(X12,X13),X14)) = k4_xboole_0(X11,k2_xboole_0(X12,k2_xboole_0(X13,X14)))) )),
% 7.14/1.29    inference(forward_demodulation,[],[f168,f31])).
% 7.14/1.29  fof(f168,plain,(
% 7.14/1.29    ( ! [X14,X12,X13,X11] : (k4_xboole_0(k4_xboole_0(X11,X12),k2_xboole_0(X13,X14)) = k4_xboole_0(X11,k2_xboole_0(k2_xboole_0(X12,X13),X14))) )),
% 7.14/1.29    inference(forward_demodulation,[],[f145,f31])).
% 7.14/1.29  fof(f145,plain,(
% 7.14/1.29    ( ! [X14,X12,X13,X11] : (k4_xboole_0(k4_xboole_0(X11,X12),k2_xboole_0(X13,X14)) = k4_xboole_0(k4_xboole_0(X11,k2_xboole_0(X12,X13)),X14)) )),
% 7.14/1.29    inference(superposition,[],[f31,f31])).
% 7.14/1.29  fof(f17499,plain,(
% 7.14/1.29    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X2,sK1))) )),
% 7.14/1.29    inference(superposition,[],[f17344,f31])).
% 7.14/1.29  fof(f17344,plain,(
% 7.14/1.29    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X4),sK1)) )),
% 7.14/1.29    inference(superposition,[],[f5082,f148])).
% 7.14/1.30  fof(f5082,plain,(
% 7.14/1.30    ( ! [X6,X7] : (k4_xboole_0(X7,k2_xboole_0(sK1,k4_xboole_0(sK0,X6))) = k4_xboole_0(X7,sK1)) )),
% 7.14/1.30    inference(forward_demodulation,[],[f5043,f76])).
% 7.14/1.30  fof(f76,plain,(
% 7.14/1.30    sK1 = k2_xboole_0(sK1,sK0)),
% 7.14/1.30    inference(forward_demodulation,[],[f70,f21])).
% 7.14/1.30  fof(f70,plain,(
% 7.14/1.30    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 7.14/1.30    inference(superposition,[],[f26,f36])).
% 7.14/1.30  fof(f36,plain,(
% 7.14/1.30    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 7.14/1.30    inference(resolution,[],[f30,f18])).
% 7.14/1.30  fof(f18,plain,(
% 7.14/1.30    r1_tarski(sK0,sK1)),
% 7.14/1.30    inference(cnf_transformation,[],[f15])).
% 7.14/1.30  fof(f5043,plain,(
% 7.14/1.30    ( ! [X6,X7] : (k4_xboole_0(X7,k2_xboole_0(sK1,k4_xboole_0(sK0,X6))) = k4_xboole_0(X7,k2_xboole_0(sK1,sK0))) )),
% 7.14/1.30    inference(superposition,[],[f4902,f75])).
% 7.14/1.30  fof(f75,plain,(
% 7.14/1.30    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4) )),
% 7.14/1.30    inference(forward_demodulation,[],[f69,f21])).
% 7.14/1.30  fof(f69,plain,(
% 7.14/1.30    ( ! [X4,X5] : (k2_xboole_0(X4,k4_xboole_0(X4,X5)) = k2_xboole_0(X4,k1_xboole_0)) )),
% 7.14/1.30    inference(superposition,[],[f26,f39])).
% 7.14/1.30  fof(f4902,plain,(
% 7.14/1.30    ( ! [X64,X63] : (k4_xboole_0(X63,k2_xboole_0(sK1,k2_xboole_0(sK0,X64))) = k4_xboole_0(X63,k2_xboole_0(sK1,X64))) )),
% 7.14/1.30    inference(superposition,[],[f169,f76])).
% 7.14/1.30  fof(f155,plain,(
% 7.14/1.30    ( ! [X12,X10,X11] : (k1_xboole_0 != k4_xboole_0(X10,k2_xboole_0(X11,X12)) | r1_tarski(k4_xboole_0(X10,X11),X12)) )),
% 7.14/1.30    inference(superposition,[],[f29,f31])).
% 7.14/1.30  fof(f46812,plain,(
% 7.14/1.30    ( ! [X1] : (r1_xboole_0(sK2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,k1_xboole_0))))) )),
% 7.14/1.30    inference(superposition,[],[f46640,f388])).
% 7.14/1.30  fof(f388,plain,(
% 7.14/1.30    ( ! [X6,X7,X5] : (k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X5,X6))) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))) )),
% 7.14/1.30    inference(forward_demodulation,[],[f357,f31])).
% 7.14/1.30  fof(f357,plain,(
% 7.14/1.30    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X7))) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X5,X6)))) )),
% 7.14/1.30    inference(superposition,[],[f32,f31])).
% 7.14/1.30  fof(f46640,plain,(
% 7.14/1.30    ( ! [X47] : (r1_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X47)))) )),
% 7.14/1.30    inference(superposition,[],[f34835,f10807])).
% 7.14/1.30  fof(f10807,plain,(
% 7.14/1.30    ( ! [X1] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X1))) )),
% 7.14/1.30    inference(forward_demodulation,[],[f10786,f31])).
% 7.14/1.30  fof(f10786,plain,(
% 7.14/1.30    ( ! [X1] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X1)) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X1)) )),
% 7.14/1.30    inference(superposition,[],[f31,f10569])).
% 7.14/1.30  fof(f34835,plain,(
% 7.14/1.30    ( ! [X30,X28,X29] : (r1_xboole_0(X28,k4_xboole_0(X30,k2_xboole_0(X28,X29)))) )),
% 7.14/1.30    inference(superposition,[],[f26769,f74])).
% 7.14/1.30  fof(f74,plain,(
% 7.14/1.30    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 7.14/1.30    inference(forward_demodulation,[],[f68,f21])).
% 7.14/1.30  fof(f68,plain,(
% 7.14/1.30    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) )),
% 7.14/1.30    inference(superposition,[],[f26,f37])).
% 7.14/1.30  fof(f37,plain,(
% 7.14/1.30    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.14/1.30    inference(resolution,[],[f30,f22])).
% 7.14/1.30  fof(f22,plain,(
% 7.14/1.30    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.14/1.30    inference(cnf_transformation,[],[f9])).
% 7.14/1.30  fof(f9,axiom,(
% 7.14/1.30    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.14/1.30    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 7.14/1.30  fof(f26769,plain,(
% 7.14/1.30    ( ! [X39,X41,X40] : (r1_xboole_0(X41,k4_xboole_0(X39,k2_xboole_0(X40,X41)))) )),
% 7.14/1.30    inference(superposition,[],[f26661,f31])).
% 7.14/1.30  fof(f26661,plain,(
% 7.14/1.30    ( ! [X14,X15] : (r1_xboole_0(X14,k4_xboole_0(X15,X14))) )),
% 7.14/1.30    inference(trivial_inequality_removal,[],[f26574])).
% 7.14/1.30  fof(f26574,plain,(
% 7.14/1.30    ( ! [X14,X15] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X14,k4_xboole_0(X15,X14))) )),
% 7.14/1.30    inference(superposition,[],[f33,f12317])).
% 7.14/1.30  fof(f12317,plain,(
% 7.14/1.30    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 7.14/1.30    inference(forward_demodulation,[],[f12316,f148])).
% 7.14/1.30  fof(f12316,plain,(
% 7.14/1.30    ( ! [X0,X1] : (k4_xboole_0(X1,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 7.14/1.30    inference(forward_demodulation,[],[f11833,f26])).
% 7.14/1.30  fof(f11833,plain,(
% 7.14/1.30    ( ! [X0,X1] : (k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 7.14/1.30    inference(superposition,[],[f388,f154])).
% 7.14/1.30  fof(f154,plain,(
% 7.14/1.30    ( ! [X8,X7,X9] : (k2_xboole_0(X9,k4_xboole_0(X7,X8)) = k2_xboole_0(X9,k4_xboole_0(X7,k2_xboole_0(X8,X9)))) )),
% 7.14/1.30    inference(superposition,[],[f26,f31])).
% 7.14/1.30  fof(f33,plain,(
% 7.14/1.30    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.14/1.30    inference(definition_unfolding,[],[f28,f25])).
% 7.14/1.30  fof(f28,plain,(
% 7.14/1.30    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.14/1.30    inference(cnf_transformation,[],[f16])).
% 7.14/1.30  fof(f29,plain,(
% 7.14/1.30    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 7.14/1.30    inference(cnf_transformation,[],[f17])).
% 7.14/1.30  fof(f363,plain,(
% 7.14/1.30    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,k4_xboole_0(X1,X0)) | r1_xboole_0(X0,X1)) )),
% 7.14/1.30    inference(superposition,[],[f33,f32])).
% 7.14/1.30  % SZS output end Proof for theBenchmark
% 7.14/1.30  % (21362)------------------------------
% 7.14/1.30  % (21362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.14/1.30  % (21362)Termination reason: Refutation
% 7.14/1.30  
% 7.14/1.30  % (21362)Memory used [KB]: 19445
% 7.14/1.30  % (21362)Time elapsed: 0.873 s
% 7.14/1.30  % (21362)------------------------------
% 7.14/1.30  % (21362)------------------------------
% 7.14/1.30  % (21344)Success in time 0.94 s
%------------------------------------------------------------------------------
