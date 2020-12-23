%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:04 EST 2020

% Result     : Theorem 4.75s
% Output     : Refutation 4.75s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 820 expanded)
%              Number of leaves         :   16 ( 219 expanded)
%              Depth                    :   19
%              Number of atoms          :  194 (1784 expanded)
%              Number of equality atoms :  100 ( 714 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7432,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f7401])).

fof(f7401,plain,(
    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f1501,f6360])).

fof(f6360,plain,(
    ! [X6,X7] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X6),X7)) = k1_setfam_1(k1_enumset1(X7,X7,k9_relat_1(sK2,X6))) ),
    inference(forward_demodulation,[],[f6359,f215])).

fof(f215,plain,(
    ! [X84] : k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X84))) = k9_relat_1(sK2,X84) ),
    inference(forward_demodulation,[],[f214,f110])).

fof(f110,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0) ),
    inference(backward_demodulation,[],[f95,f102])).

fof(f102,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f95,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f38,f62])).

fof(f62,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f214,plain,(
    ! [X84] : k9_relat_1(k7_relat_1(sK2,X84),k1_relat_1(k7_relat_1(sK2,X84))) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X84))) ),
    inference(forward_demodulation,[],[f197,f102])).

fof(f197,plain,(
    ! [X84] : k9_relat_1(k7_relat_1(sK2,X84),k1_relat_1(k7_relat_1(sK2,X84))) = k2_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X84)))) ),
    inference(superposition,[],[f103,f163])).

fof(f163,plain,(
    ! [X0] : k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(resolution,[],[f152,f35])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(k7_relat_1(sK2,X1))) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(sK2,X1))) ) ),
    inference(resolution,[],[f52,f69])).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    inference(resolution,[],[f43,f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f103,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) = k9_relat_1(k7_relat_1(sK2,X1),X2) ),
    inference(resolution,[],[f44,f62])).

fof(f6359,plain,(
    ! [X6,X7] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X6),X7)) = k1_setfam_1(k1_enumset1(X7,X7,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X6))))) ),
    inference(forward_demodulation,[],[f6316,f2056])).

fof(f2056,plain,(
    ! [X26,X25] : k9_relat_1(k7_relat_1(sK2,X25),k10_relat_1(k7_relat_1(sK2,X25),X26)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X25),X26)) ),
    inference(backward_demodulation,[],[f1527,f2055])).

fof(f2055,plain,(
    ! [X12,X11] : k9_relat_1(k7_relat_1(sK2,X11),k10_relat_1(sK2,X12)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X11),X12)) ),
    inference(forward_demodulation,[],[f2048,f1599])).

fof(f1599,plain,(
    ! [X2,X3] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3)) = k9_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3)),k10_relat_1(k7_relat_1(sK2,X2),X3)) ),
    inference(superposition,[],[f110,f1590])).

fof(f1590,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))) ),
    inference(forward_demodulation,[],[f1583,f1005])).

fof(f1005,plain,(
    ! [X5] : k7_relat_1(sK2,X5) = k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f951,f637])).

fof(f637,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(backward_demodulation,[],[f163,f636])).

fof(f636,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(forward_demodulation,[],[f623,f255])).

fof(f255,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)) ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f623,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0))) ),
    inference(resolution,[],[f57,f35])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f951,plain,(
    ! [X5] : k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(sK2)) = k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(k7_relat_1(sK2,X5))) ),
    inference(superposition,[],[f676,f639])).

fof(f639,plain,(
    ! [X2] : k1_relat_1(k7_relat_1(sK2,X2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),k1_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f274,f636])).

fof(f274,plain,(
    ! [X2] : k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),k1_relat_1(sK2))) ),
    inference(superposition,[],[f256,f268])).

fof(f268,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK2))) ),
    inference(superposition,[],[f255,f55])).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f40,f40])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f256,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(sK2,X1)),k1_relat_1(k7_relat_1(sK2,X1)),X2)) ),
    inference(resolution,[],[f56,f62])).

fof(f676,plain,(
    ! [X2,X1] : k7_relat_1(k7_relat_1(sK2,X1),X2) = k7_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2))) ),
    inference(forward_demodulation,[],[f624,f256])).

fof(f624,plain,(
    ! [X2,X1] : k7_relat_1(k7_relat_1(sK2,X1),X2) = k7_relat_1(k7_relat_1(sK2,X1),k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(sK2,X1)),k1_relat_1(k7_relat_1(sK2,X1)),X2))) ),
    inference(resolution,[],[f57,f62])).

fof(f1583,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))) = k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),k1_relat_1(sK2)),X1) ),
    inference(superposition,[],[f1489,f255])).

fof(f1489,plain,(
    ! [X4,X2,X3] : k10_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3),X4) = k1_setfam_1(k1_enumset1(X3,X3,k10_relat_1(k7_relat_1(sK2,X2),X4))) ),
    inference(resolution,[],[f59,f62])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f2048,plain,(
    ! [X12,X11] : k9_relat_1(k7_relat_1(sK2,X11),k10_relat_1(sK2,X12)) = k9_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X11),X12)),k10_relat_1(k7_relat_1(sK2,X11),X12)) ),
    inference(backward_demodulation,[],[f1521,f1875])).

fof(f1875,plain,(
    ! [X6,X7] : k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X6),X7)) = k7_relat_1(k7_relat_1(sK2,X6),k10_relat_1(sK2,X7)) ),
    inference(superposition,[],[f1856,f1488])).

fof(f1488,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f59,f35])).

fof(f1856,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(resolution,[],[f60,f35])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f1521,plain,(
    ! [X12,X11] : k9_relat_1(k7_relat_1(sK2,X11),k10_relat_1(sK2,X12)) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X11),k10_relat_1(sK2,X12)),k10_relat_1(k7_relat_1(sK2,X11),X12)) ),
    inference(superposition,[],[f111,f1508])).

fof(f1508,plain,(
    ! [X2,X1] : k10_relat_1(k7_relat_1(sK2,X1),X2) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),k10_relat_1(sK2,X2))) ),
    inference(forward_demodulation,[],[f1505,f636])).

fof(f1505,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),k10_relat_1(sK2,X2))) = k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X1))),X2) ),
    inference(superposition,[],[f1488,f256])).

fof(f111,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2))) = k9_relat_1(k7_relat_1(sK2,X1),X2) ),
    inference(backward_demodulation,[],[f96,f103])).

fof(f96,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) ),
    inference(resolution,[],[f38,f63])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(resolution,[],[f62,f42])).

fof(f1527,plain,(
    ! [X26,X25] : k9_relat_1(k7_relat_1(sK2,X25),k10_relat_1(sK2,X26)) = k9_relat_1(k7_relat_1(sK2,X25),k10_relat_1(k7_relat_1(sK2,X25),X26)) ),
    inference(superposition,[],[f596,f1508])).

fof(f596,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) ),
    inference(superposition,[],[f574,f111])).

fof(f574,plain,(
    ! [X101,X99,X100] : k9_relat_1(k7_relat_1(k7_relat_1(sK2,X99),X100),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X101),X100))) = k9_relat_1(k7_relat_1(sK2,X99),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X101),X100))) ),
    inference(forward_demodulation,[],[f554,f103])).

fof(f554,plain,(
    ! [X101,X99,X100] : k9_relat_1(k7_relat_1(k7_relat_1(sK2,X99),X100),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X101),X100))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X99),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X101),X100)))) ),
    inference(superposition,[],[f104,f297])).

fof(f297,plain,(
    ! [X4,X2,X3] : k7_relat_1(k7_relat_1(sK2,X2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X4),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4))) ),
    inference(resolution,[],[f153,f62])).

fof(f153,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4))) = k7_relat_1(k7_relat_1(X2,X4),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4))) ) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X2,X1] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)),X2) ),
    inference(resolution,[],[f43,f62])).

fof(f104,plain,(
    ! [X4,X5,X3] : k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4),X5)) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4),X5) ),
    inference(resolution,[],[f44,f63])).

fof(f6316,plain,(
    ! [X6,X7] : k1_setfam_1(k1_enumset1(X7,X7,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X6))))) = k9_relat_1(k7_relat_1(sK2,X6),k10_relat_1(k7_relat_1(sK2,X6),X7)) ),
    inference(superposition,[],[f2830,f636])).

fof(f2830,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(sK2,X1))) ),
    inference(forward_demodulation,[],[f2829,f110])).

fof(f2829,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1))))) ),
    inference(subsumption_resolution,[],[f2815,f62])).

fof(f2815,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1)))))
      | ~ v1_relat_1(k7_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f58,f77])).

fof(f77,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK2,X0)) ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f76,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK2,X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f1501,plain,(
    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(backward_demodulation,[],[f61,f1488])).

fof(f61,plain,(
    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(backward_demodulation,[],[f54,f55])).

fof(f54,plain,(
    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) ),
    inference(definition_unfolding,[],[f37,f53,f53])).

fof(f37,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:58:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (27906)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.45  % (27914)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (27904)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (27909)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (27913)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (27903)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (27920)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (27908)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (27910)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (27905)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (27907)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (27915)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (27917)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (27911)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (27918)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (27912)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (27919)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (27916)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 4.75/0.97  % (27916)Refutation found. Thanks to Tanya!
% 4.75/0.97  % SZS status Theorem for theBenchmark
% 4.75/0.97  % SZS output start Proof for theBenchmark
% 4.75/0.97  fof(f7432,plain,(
% 4.75/0.97    $false),
% 4.75/0.97    inference(trivial_inequality_removal,[],[f7401])).
% 4.75/0.97  fof(f7401,plain,(
% 4.75/0.97    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),
% 4.75/0.97    inference(superposition,[],[f1501,f6360])).
% 4.75/0.97  fof(f6360,plain,(
% 4.75/0.97    ( ! [X6,X7] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X6),X7)) = k1_setfam_1(k1_enumset1(X7,X7,k9_relat_1(sK2,X6)))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f6359,f215])).
% 4.75/0.97  fof(f215,plain,(
% 4.75/0.97    ( ! [X84] : (k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X84))) = k9_relat_1(sK2,X84)) )),
% 4.75/0.97    inference(forward_demodulation,[],[f214,f110])).
% 4.75/0.97  fof(f110,plain,(
% 4.75/0.97    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)) )),
% 4.75/0.97    inference(backward_demodulation,[],[f95,f102])).
% 4.75/0.97  fof(f102,plain,(
% 4.75/0.97    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 4.75/0.97    inference(resolution,[],[f44,f35])).
% 4.75/0.97  fof(f35,plain,(
% 4.75/0.97    v1_relat_1(sK2)),
% 4.75/0.97    inference(cnf_transformation,[],[f34])).
% 4.75/0.97  fof(f34,plain,(
% 4.75/0.97    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 4.75/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f33])).
% 4.75/0.97  fof(f33,plain,(
% 4.75/0.97    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 4.75/0.97    introduced(choice_axiom,[])).
% 4.75/0.97  fof(f18,plain,(
% 4.75/0.97    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.75/0.97    inference(flattening,[],[f17])).
% 4.75/0.97  fof(f17,plain,(
% 4.75/0.97    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.75/0.97    inference(ennf_transformation,[],[f16])).
% 4.75/0.97  fof(f16,negated_conjecture,(
% 4.75/0.97    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 4.75/0.97    inference(negated_conjecture,[],[f15])).
% 4.75/0.97  fof(f15,conjecture,(
% 4.75/0.97    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).
% 4.75/0.97  fof(f44,plain,(
% 4.75/0.97    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f22])).
% 4.75/0.97  fof(f22,plain,(
% 4.75/0.97    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.75/0.97    inference(ennf_transformation,[],[f8])).
% 4.75/0.97  fof(f8,axiom,(
% 4.75/0.97    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 4.75/0.97  fof(f95,plain,(
% 4.75/0.97    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 4.75/0.97    inference(resolution,[],[f38,f62])).
% 4.75/0.97  fof(f62,plain,(
% 4.75/0.97    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 4.75/0.97    inference(resolution,[],[f42,f35])).
% 4.75/0.97  fof(f42,plain,(
% 4.75/0.97    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 4.75/0.97    inference(cnf_transformation,[],[f20])).
% 4.75/0.97  fof(f20,plain,(
% 4.75/0.97    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.75/0.97    inference(ennf_transformation,[],[f4])).
% 4.75/0.97  fof(f4,axiom,(
% 4.75/0.97    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 4.75/0.97  fof(f38,plain,(
% 4.75/0.97    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f19])).
% 4.75/0.97  fof(f19,plain,(
% 4.75/0.97    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 4.75/0.97    inference(ennf_transformation,[],[f7])).
% 4.75/0.97  fof(f7,axiom,(
% 4.75/0.97    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 4.75/0.97  fof(f214,plain,(
% 4.75/0.97    ( ! [X84] : (k9_relat_1(k7_relat_1(sK2,X84),k1_relat_1(k7_relat_1(sK2,X84))) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X84)))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f197,f102])).
% 4.75/0.97  fof(f197,plain,(
% 4.75/0.97    ( ! [X84] : (k9_relat_1(k7_relat_1(sK2,X84),k1_relat_1(k7_relat_1(sK2,X84))) = k2_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X84))))) )),
% 4.75/0.97    inference(superposition,[],[f103,f163])).
% 4.75/0.97  fof(f163,plain,(
% 4.75/0.97    ( ! [X0] : (k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) = k7_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 4.75/0.97    inference(resolution,[],[f152,f35])).
% 4.75/0.97  fof(f152,plain,(
% 4.75/0.97    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(k7_relat_1(sK2,X1))) = k7_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(sK2,X1)))) )),
% 4.75/0.97    inference(resolution,[],[f52,f69])).
% 4.75/0.97  fof(f69,plain,(
% 4.75/0.97    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) )),
% 4.75/0.97    inference(resolution,[],[f43,f35])).
% 4.75/0.97  fof(f43,plain,(
% 4.75/0.97    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f21])).
% 4.75/0.97  fof(f21,plain,(
% 4.75/0.97    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 4.75/0.97    inference(ennf_transformation,[],[f10])).
% 4.75/0.97  fof(f10,axiom,(
% 4.75/0.97    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 4.75/0.97  fof(f52,plain,(
% 4.75/0.97    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f32])).
% 4.75/0.97  fof(f32,plain,(
% 4.75/0.97    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 4.75/0.97    inference(flattening,[],[f31])).
% 4.75/0.97  fof(f31,plain,(
% 4.75/0.97    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 4.75/0.97    inference(ennf_transformation,[],[f6])).
% 4.75/0.97  fof(f6,axiom,(
% 4.75/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 4.75/0.97  fof(f103,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) = k9_relat_1(k7_relat_1(sK2,X1),X2)) )),
% 4.75/0.97    inference(resolution,[],[f44,f62])).
% 4.75/0.97  fof(f6359,plain,(
% 4.75/0.97    ( ! [X6,X7] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X6),X7)) = k1_setfam_1(k1_enumset1(X7,X7,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X6)))))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f6316,f2056])).
% 4.75/0.97  fof(f2056,plain,(
% 4.75/0.97    ( ! [X26,X25] : (k9_relat_1(k7_relat_1(sK2,X25),k10_relat_1(k7_relat_1(sK2,X25),X26)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X25),X26))) )),
% 4.75/0.97    inference(backward_demodulation,[],[f1527,f2055])).
% 4.75/0.97  fof(f2055,plain,(
% 4.75/0.97    ( ! [X12,X11] : (k9_relat_1(k7_relat_1(sK2,X11),k10_relat_1(sK2,X12)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X11),X12))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f2048,f1599])).
% 4.75/0.97  fof(f1599,plain,(
% 4.75/0.97    ( ! [X2,X3] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3)) = k9_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3)),k10_relat_1(k7_relat_1(sK2,X2),X3))) )),
% 4.75/0.97    inference(superposition,[],[f110,f1590])).
% 4.75/0.97  fof(f1590,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f1583,f1005])).
% 4.75/0.97  fof(f1005,plain,(
% 4.75/0.97    ( ! [X5] : (k7_relat_1(sK2,X5) = k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(sK2))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f951,f637])).
% 4.75/0.97  fof(f637,plain,(
% 4.75/0.97    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 4.75/0.97    inference(backward_demodulation,[],[f163,f636])).
% 4.75/0.97  fof(f636,plain,(
% 4.75/0.97    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f623,f255])).
% 4.75/0.97  fof(f255,plain,(
% 4.75/0.97    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0))) )),
% 4.75/0.97    inference(resolution,[],[f56,f35])).
% 4.75/0.97  fof(f56,plain,(
% 4.75/0.97    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 4.75/0.97    inference(definition_unfolding,[],[f45,f53])).
% 4.75/0.97  fof(f53,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 4.75/0.97    inference(definition_unfolding,[],[f41,f40])).
% 4.75/0.97  fof(f40,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f2])).
% 4.75/0.97  fof(f2,axiom,(
% 4.75/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.75/0.97  fof(f41,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f3])).
% 4.75/0.97  fof(f3,axiom,(
% 4.75/0.97    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 4.75/0.97  fof(f45,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f23])).
% 4.75/0.97  fof(f23,plain,(
% 4.75/0.97    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 4.75/0.97    inference(ennf_transformation,[],[f11])).
% 4.75/0.97  fof(f11,axiom,(
% 4.75/0.97    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 4.75/0.97  fof(f623,plain,(
% 4.75/0.97    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)))) )),
% 4.75/0.97    inference(resolution,[],[f57,f35])).
% 4.75/0.97  fof(f57,plain,(
% 4.75/0.97    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 4.75/0.97    inference(definition_unfolding,[],[f46,f53])).
% 4.75/0.97  fof(f46,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f24])).
% 4.75/0.97  fof(f24,plain,(
% 4.75/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.75/0.97    inference(ennf_transformation,[],[f9])).
% 4.75/0.97  fof(f9,axiom,(
% 4.75/0.97    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 4.75/0.97  fof(f951,plain,(
% 4.75/0.97    ( ! [X5] : (k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(sK2)) = k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(k7_relat_1(sK2,X5)))) )),
% 4.75/0.97    inference(superposition,[],[f676,f639])).
% 4.75/0.97  fof(f639,plain,(
% 4.75/0.97    ( ! [X2] : (k1_relat_1(k7_relat_1(sK2,X2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),k1_relat_1(sK2)))) )),
% 4.75/0.97    inference(backward_demodulation,[],[f274,f636])).
% 4.75/0.97  fof(f274,plain,(
% 4.75/0.97    ( ! [X2] : (k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),k1_relat_1(sK2)))) )),
% 4.75/0.97    inference(superposition,[],[f256,f268])).
% 4.75/0.97  fof(f268,plain,(
% 4.75/0.97    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK2)))) )),
% 4.75/0.97    inference(superposition,[],[f255,f55])).
% 4.75/0.97  fof(f55,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 4.75/0.97    inference(definition_unfolding,[],[f39,f40,f40])).
% 4.75/0.97  fof(f39,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f1])).
% 4.75/0.97  fof(f1,axiom,(
% 4.75/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 4.75/0.97  fof(f256,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(sK2,X1)),k1_relat_1(k7_relat_1(sK2,X1)),X2))) )),
% 4.75/0.97    inference(resolution,[],[f56,f62])).
% 4.75/0.97  fof(f676,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k7_relat_1(k7_relat_1(sK2,X1),X2) = k7_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f624,f256])).
% 4.75/0.97  fof(f624,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k7_relat_1(k7_relat_1(sK2,X1),X2) = k7_relat_1(k7_relat_1(sK2,X1),k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(sK2,X1)),k1_relat_1(k7_relat_1(sK2,X1)),X2)))) )),
% 4.75/0.97    inference(resolution,[],[f57,f62])).
% 4.75/0.97  fof(f1583,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1))) = k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),k1_relat_1(sK2)),X1)) )),
% 4.75/0.97    inference(superposition,[],[f1489,f255])).
% 4.75/0.97  fof(f1489,plain,(
% 4.75/0.97    ( ! [X4,X2,X3] : (k10_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3),X4) = k1_setfam_1(k1_enumset1(X3,X3,k10_relat_1(k7_relat_1(sK2,X2),X4)))) )),
% 4.75/0.97    inference(resolution,[],[f59,f62])).
% 4.75/0.97  fof(f59,plain,(
% 4.75/0.97    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 4.75/0.97    inference(definition_unfolding,[],[f50,f53])).
% 4.75/0.97  fof(f50,plain,(
% 4.75/0.97    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f29])).
% 4.75/0.97  fof(f29,plain,(
% 4.75/0.97    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 4.75/0.97    inference(ennf_transformation,[],[f13])).
% 4.75/0.97  fof(f13,axiom,(
% 4.75/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 4.75/0.97  fof(f2048,plain,(
% 4.75/0.97    ( ! [X12,X11] : (k9_relat_1(k7_relat_1(sK2,X11),k10_relat_1(sK2,X12)) = k9_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X11),X12)),k10_relat_1(k7_relat_1(sK2,X11),X12))) )),
% 4.75/0.97    inference(backward_demodulation,[],[f1521,f1875])).
% 4.75/0.97  fof(f1875,plain,(
% 4.75/0.97    ( ! [X6,X7] : (k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X6),X7)) = k7_relat_1(k7_relat_1(sK2,X6),k10_relat_1(sK2,X7))) )),
% 4.75/0.97    inference(superposition,[],[f1856,f1488])).
% 4.75/0.97  fof(f1488,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))) )),
% 4.75/0.97    inference(resolution,[],[f59,f35])).
% 4.75/0.97  fof(f1856,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 4.75/0.97    inference(resolution,[],[f60,f35])).
% 4.75/0.97  fof(f60,plain,(
% 4.75/0.97    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 4.75/0.97    inference(definition_unfolding,[],[f51,f53])).
% 4.75/0.97  fof(f51,plain,(
% 4.75/0.97    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f30])).
% 4.75/0.97  fof(f30,plain,(
% 4.75/0.97    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 4.75/0.97    inference(ennf_transformation,[],[f5])).
% 4.75/0.97  fof(f5,axiom,(
% 4.75/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 4.75/0.97  fof(f1521,plain,(
% 4.75/0.97    ( ! [X12,X11] : (k9_relat_1(k7_relat_1(sK2,X11),k10_relat_1(sK2,X12)) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X11),k10_relat_1(sK2,X12)),k10_relat_1(k7_relat_1(sK2,X11),X12))) )),
% 4.75/0.97    inference(superposition,[],[f111,f1508])).
% 4.75/0.97  fof(f1508,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k10_relat_1(k7_relat_1(sK2,X1),X2) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),k10_relat_1(sK2,X2)))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f1505,f636])).
% 4.75/0.97  fof(f1505,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),k10_relat_1(sK2,X2))) = k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X1))),X2)) )),
% 4.75/0.97    inference(superposition,[],[f1488,f256])).
% 4.75/0.97  fof(f111,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2))) = k9_relat_1(k7_relat_1(sK2,X1),X2)) )),
% 4.75/0.97    inference(backward_demodulation,[],[f96,f103])).
% 4.75/0.97  fof(f96,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2))) )),
% 4.75/0.97    inference(resolution,[],[f38,f63])).
% 4.75/0.97  fof(f63,plain,(
% 4.75/0.97    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 4.75/0.97    inference(resolution,[],[f62,f42])).
% 4.75/0.97  fof(f1527,plain,(
% 4.75/0.97    ( ! [X26,X25] : (k9_relat_1(k7_relat_1(sK2,X25),k10_relat_1(sK2,X26)) = k9_relat_1(k7_relat_1(sK2,X25),k10_relat_1(k7_relat_1(sK2,X25),X26))) )),
% 4.75/0.97    inference(superposition,[],[f596,f1508])).
% 4.75/0.97  fof(f596,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)))) )),
% 4.75/0.97    inference(superposition,[],[f574,f111])).
% 4.75/0.97  fof(f574,plain,(
% 4.75/0.97    ( ! [X101,X99,X100] : (k9_relat_1(k7_relat_1(k7_relat_1(sK2,X99),X100),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X101),X100))) = k9_relat_1(k7_relat_1(sK2,X99),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X101),X100)))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f554,f103])).
% 4.75/0.97  fof(f554,plain,(
% 4.75/0.97    ( ! [X101,X99,X100] : (k9_relat_1(k7_relat_1(k7_relat_1(sK2,X99),X100),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X101),X100))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X99),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X101),X100))))) )),
% 4.75/0.97    inference(superposition,[],[f104,f297])).
% 4.75/0.97  fof(f297,plain,(
% 4.75/0.97    ( ! [X4,X2,X3] : (k7_relat_1(k7_relat_1(sK2,X2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X4),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4)))) )),
% 4.75/0.97    inference(resolution,[],[f153,f62])).
% 4.75/0.97  fof(f153,plain,(
% 4.75/0.97    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k7_relat_1(X2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4))) = k7_relat_1(k7_relat_1(X2,X4),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4)))) )),
% 4.75/0.97    inference(resolution,[],[f52,f70])).
% 4.75/0.97  fof(f70,plain,(
% 4.75/0.97    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)),X2)) )),
% 4.75/0.97    inference(resolution,[],[f43,f62])).
% 4.75/0.97  fof(f104,plain,(
% 4.75/0.97    ( ! [X4,X5,X3] : (k2_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4),X5)) = k9_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4),X5)) )),
% 4.75/0.97    inference(resolution,[],[f44,f63])).
% 4.75/0.97  fof(f6316,plain,(
% 4.75/0.97    ( ! [X6,X7] : (k1_setfam_1(k1_enumset1(X7,X7,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X6))))) = k9_relat_1(k7_relat_1(sK2,X6),k10_relat_1(k7_relat_1(sK2,X6),X7))) )),
% 4.75/0.97    inference(superposition,[],[f2830,f636])).
% 4.75/0.97  fof(f2830,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(sK2,X1)))) )),
% 4.75/0.97    inference(forward_demodulation,[],[f2829,f110])).
% 4.75/0.97  fof(f2829,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1)))))) )),
% 4.75/0.97    inference(subsumption_resolution,[],[f2815,f62])).
% 4.75/0.97  fof(f2815,plain,(
% 4.75/0.97    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1))))) | ~v1_relat_1(k7_relat_1(sK2,X1))) )),
% 4.75/0.97    inference(resolution,[],[f58,f77])).
% 4.75/0.97  fof(f77,plain,(
% 4.75/0.97    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0))) )),
% 4.75/0.97    inference(subsumption_resolution,[],[f76,f35])).
% 4.75/0.97  fof(f76,plain,(
% 4.75/0.97    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(sK2)) )),
% 4.75/0.97    inference(resolution,[],[f49,f36])).
% 4.75/0.97  fof(f36,plain,(
% 4.75/0.97    v1_funct_1(sK2)),
% 4.75/0.97    inference(cnf_transformation,[],[f34])).
% 4.75/0.97  fof(f49,plain,(
% 4.75/0.97    ( ! [X0,X1] : (~v1_funct_1(X0) | v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f28])).
% 4.75/0.97  fof(f28,plain,(
% 4.75/0.97    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.75/0.97    inference(flattening,[],[f27])).
% 4.75/0.97  fof(f27,plain,(
% 4.75/0.97    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.75/0.97    inference(ennf_transformation,[],[f12])).
% 4.75/0.97  fof(f12,axiom,(
% 4.75/0.97    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 4.75/0.97  fof(f58,plain,(
% 4.75/0.97    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 4.75/0.97    inference(definition_unfolding,[],[f47,f53])).
% 4.75/0.97  fof(f47,plain,(
% 4.75/0.97    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.75/0.97    inference(cnf_transformation,[],[f26])).
% 4.75/0.97  fof(f26,plain,(
% 4.75/0.97    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.75/0.97    inference(flattening,[],[f25])).
% 4.75/0.97  fof(f25,plain,(
% 4.75/0.97    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.75/0.97    inference(ennf_transformation,[],[f14])).
% 4.75/0.97  fof(f14,axiom,(
% 4.75/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 4.75/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 4.75/0.97  fof(f1501,plain,(
% 4.75/0.97    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 4.75/0.97    inference(backward_demodulation,[],[f61,f1488])).
% 4.75/0.97  fof(f61,plain,(
% 4.75/0.97    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),
% 4.75/0.97    inference(backward_demodulation,[],[f54,f55])).
% 4.75/0.97  fof(f54,plain,(
% 4.75/0.97    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))),
% 4.75/0.97    inference(definition_unfolding,[],[f37,f53,f53])).
% 4.75/0.97  fof(f37,plain,(
% 4.75/0.97    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 4.75/0.97    inference(cnf_transformation,[],[f34])).
% 4.75/0.97  % SZS output end Proof for theBenchmark
% 4.75/0.97  % (27916)------------------------------
% 4.75/0.97  % (27916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.75/0.97  % (27916)Termination reason: Refutation
% 4.75/0.97  
% 4.75/0.97  % (27916)Memory used [KB]: 7291
% 4.75/0.97  % (27916)Time elapsed: 0.544 s
% 4.75/0.97  % (27916)------------------------------
% 4.75/0.97  % (27916)------------------------------
% 4.75/0.97  % (27902)Success in time 0.608 s
%------------------------------------------------------------------------------
