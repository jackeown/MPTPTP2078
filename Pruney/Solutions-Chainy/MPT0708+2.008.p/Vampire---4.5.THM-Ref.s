%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:35 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 199 expanded)
%              Number of leaves         :   16 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  168 ( 534 expanded)
%              Number of equality atoms :   57 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5365,plain,(
    $false ),
    inference(resolution,[],[f5325,f39])).

fof(f39,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
    & r1_tarski(k9_relat_1(sK2,sK0),sK1)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
        & r1_tarski(k9_relat_1(X2,X0),X1)
        & r1_tarski(X0,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK2,sK1))
      & r1_tarski(k9_relat_1(sK2,sK0),sK1)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k10_relat_1(X2,X1))
      & r1_tarski(k9_relat_1(X2,X0),X1)
      & r1_tarski(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
            & r1_tarski(X0,k1_relat_1(X2)) )
         => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f5325,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(trivial_inequality_removal,[],[f5303])).

fof(f5303,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f51,f5231])).

fof(f5231,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f5228,f84])).

fof(f84,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f50,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f42,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f5228,plain,(
    r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f5208,f67])).

fof(f5208,plain,(
    r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK1)),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f1744,f3229])).

fof(f3229,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(forward_demodulation,[],[f3228,f240])).

fof(f240,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f150,f37])).

fof(f37,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK2))
      | k1_relat_1(k7_relat_1(sK2,X0)) = X0 ) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f3228,plain,(
    k1_relat_1(k7_relat_1(sK2,sK0)) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(forward_demodulation,[],[f3227,f795])).

fof(f795,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k10_relat_1(k7_relat_1(sK2,X0),k9_relat_1(sK2,X0)) ),
    inference(forward_demodulation,[],[f793,f107])).

fof(f107,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f47,f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f793,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k10_relat_1(k7_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X0))) ),
    inference(resolution,[],[f73,f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f41,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f3227,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(forward_demodulation,[],[f3187,f40])).

fof(f3187,plain,(
    k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k7_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f1143,f70])).

fof(f70,plain,(
    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f1143,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),X1))) ),
    inference(forward_demodulation,[],[f1141,f107])).

fof(f1141,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k4_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k4_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),X1))) ),
    inference(resolution,[],[f242,f35])).

fof(f242,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(k7_relat_1(X1,X2),X3) = k10_relat_1(k7_relat_1(X1,X2),k4_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),k4_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),X3))) ) ),
    inference(resolution,[],[f61,f46])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) ) ),
    inference(forward_demodulation,[],[f58,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f1744,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k10_relat_1(sK2,X1)),k4_xboole_0(X0,k10_relat_1(k7_relat_1(sK2,X0),X1))) ),
    inference(superposition,[],[f659,f248])).

fof(f248,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f62,f35])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    inference(forward_demodulation,[],[f59,f57])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f659,plain,(
    ! [X24,X25] : r1_tarski(k4_xboole_0(X24,X25),k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X24,X25)))) ),
    inference(resolution,[],[f209,f64])).

fof(f209,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(k4_xboole_0(X4,X5),X6)
      | r1_tarski(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X4,X6))) ) ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(forward_demodulation,[],[f60,f57])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:24:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (14105)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.44  % (14106)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (14100)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (14115)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (14108)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (14099)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (14103)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (14107)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (14104)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (14102)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (14112)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (14109)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (14098)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (14101)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (14110)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (14097)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (14113)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (14114)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.76/0.75  % (14098)Refutation found. Thanks to Tanya!
% 2.76/0.75  % SZS status Theorem for theBenchmark
% 2.76/0.75  % SZS output start Proof for theBenchmark
% 2.76/0.75  fof(f5365,plain,(
% 2.76/0.75    $false),
% 2.76/0.75    inference(resolution,[],[f5325,f39])).
% 2.76/0.75  fof(f39,plain,(
% 2.76/0.75    ~r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 2.76/0.75    inference(cnf_transformation,[],[f33])).
% 2.76/0.75  fof(f33,plain,(
% 2.76/0.75    ~r1_tarski(sK0,k10_relat_1(sK2,sK1)) & r1_tarski(k9_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 2.76/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32])).
% 2.76/0.75  fof(f32,plain,(
% 2.76/0.75    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,k10_relat_1(sK2,sK1)) & r1_tarski(k9_relat_1(sK2,sK0),sK1) & r1_tarski(sK0,k1_relat_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 2.76/0.75    introduced(choice_axiom,[])).
% 2.76/0.75  fof(f19,plain,(
% 2.76/0.75    ? [X0,X1,X2] : (~r1_tarski(X0,k10_relat_1(X2,X1)) & r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.76/0.75    inference(flattening,[],[f18])).
% 2.76/0.75  fof(f18,plain,(
% 2.76/0.75    ? [X0,X1,X2] : ((~r1_tarski(X0,k10_relat_1(X2,X1)) & (r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.76/0.75    inference(ennf_transformation,[],[f17])).
% 2.76/0.75  fof(f17,negated_conjecture,(
% 2.76/0.75    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.76/0.75    inference(negated_conjecture,[],[f16])).
% 2.76/0.75  fof(f16,conjecture,(
% 2.76/0.75    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 2.76/0.75  fof(f5325,plain,(
% 2.76/0.75    r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 2.76/0.75    inference(trivial_inequality_removal,[],[f5303])).
% 2.76/0.75  fof(f5303,plain,(
% 2.76/0.75    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 2.76/0.75    inference(superposition,[],[f51,f5231])).
% 2.76/0.75  fof(f5231,plain,(
% 2.76/0.75    k1_xboole_0 = k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),
% 2.76/0.75    inference(resolution,[],[f5228,f84])).
% 2.76/0.75  fof(f84,plain,(
% 2.76/0.75    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 2.76/0.75    inference(superposition,[],[f50,f67])).
% 2.76/0.75  fof(f67,plain,(
% 2.76/0.75    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.76/0.75    inference(resolution,[],[f52,f64])).
% 2.76/0.75  fof(f64,plain,(
% 2.76/0.75    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.76/0.75    inference(superposition,[],[f42,f40])).
% 2.76/0.75  fof(f40,plain,(
% 2.76/0.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.76/0.75    inference(cnf_transformation,[],[f6])).
% 2.76/0.75  fof(f6,axiom,(
% 2.76/0.75    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.76/0.75  fof(f42,plain,(
% 2.76/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f4])).
% 2.76/0.75  fof(f4,axiom,(
% 2.76/0.75    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.76/0.75  fof(f52,plain,(
% 2.76/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.76/0.75    inference(cnf_transformation,[],[f34])).
% 2.76/0.75  fof(f34,plain,(
% 2.76/0.75    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.76/0.75    inference(nnf_transformation,[],[f1])).
% 2.76/0.75  fof(f1,axiom,(
% 2.76/0.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.76/0.75  fof(f50,plain,(
% 2.76/0.75    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 2.76/0.75    inference(cnf_transformation,[],[f26])).
% 2.76/0.75  fof(f26,plain,(
% 2.76/0.75    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 2.76/0.75    inference(ennf_transformation,[],[f5])).
% 2.76/0.75  fof(f5,axiom,(
% 2.76/0.75    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 2.76/0.75  fof(f5228,plain,(
% 2.76/0.75    r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK1)),k1_xboole_0)),
% 2.76/0.75    inference(forward_demodulation,[],[f5208,f67])).
% 2.76/0.75  fof(f5208,plain,(
% 2.76/0.75    r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK1)),k4_xboole_0(sK0,sK0))),
% 2.76/0.75    inference(superposition,[],[f1744,f3229])).
% 2.76/0.75  fof(f3229,plain,(
% 2.76/0.75    sK0 = k10_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 2.76/0.75    inference(forward_demodulation,[],[f3228,f240])).
% 2.76/0.75  fof(f240,plain,(
% 2.76/0.75    sK0 = k1_relat_1(k7_relat_1(sK2,sK0))),
% 2.76/0.75    inference(resolution,[],[f150,f37])).
% 2.76/0.75  fof(f37,plain,(
% 2.76/0.75    r1_tarski(sK0,k1_relat_1(sK2))),
% 2.76/0.75    inference(cnf_transformation,[],[f33])).
% 2.76/0.75  fof(f150,plain,(
% 2.76/0.75    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK2)) | k1_relat_1(k7_relat_1(sK2,X0)) = X0) )),
% 2.76/0.75    inference(resolution,[],[f49,f35])).
% 2.76/0.75  fof(f35,plain,(
% 2.76/0.75    v1_relat_1(sK2)),
% 2.76/0.75    inference(cnf_transformation,[],[f33])).
% 2.76/0.75  fof(f49,plain,(
% 2.76/0.75    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 2.76/0.75    inference(cnf_transformation,[],[f25])).
% 2.76/0.75  fof(f25,plain,(
% 2.76/0.75    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.76/0.75    inference(flattening,[],[f24])).
% 2.76/0.75  fof(f24,plain,(
% 2.76/0.75    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.76/0.75    inference(ennf_transformation,[],[f14])).
% 2.76/0.75  fof(f14,axiom,(
% 2.76/0.75    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 2.76/0.75  fof(f3228,plain,(
% 2.76/0.75    k1_relat_1(k7_relat_1(sK2,sK0)) = k10_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 2.76/0.75    inference(forward_demodulation,[],[f3227,f795])).
% 2.76/0.75  fof(f795,plain,(
% 2.76/0.75    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k10_relat_1(k7_relat_1(sK2,X0),k9_relat_1(sK2,X0))) )),
% 2.76/0.75    inference(forward_demodulation,[],[f793,f107])).
% 2.76/0.75  fof(f107,plain,(
% 2.76/0.75    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 2.76/0.75    inference(resolution,[],[f47,f35])).
% 2.76/0.75  fof(f47,plain,(
% 2.76/0.75    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f22])).
% 2.76/0.75  fof(f22,plain,(
% 2.76/0.75    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.76/0.75    inference(ennf_transformation,[],[f11])).
% 2.76/0.75  fof(f11,axiom,(
% 2.76/0.75    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.76/0.75  fof(f793,plain,(
% 2.76/0.75    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k10_relat_1(k7_relat_1(sK2,X0),k2_relat_1(k7_relat_1(sK2,X0)))) )),
% 2.76/0.75    inference(resolution,[],[f73,f35])).
% 2.76/0.75  fof(f73,plain,(
% 2.76/0.75    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1)))) )),
% 2.76/0.75    inference(resolution,[],[f41,f46])).
% 2.76/0.75  fof(f46,plain,(
% 2.76/0.75    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f21])).
% 2.76/0.75  fof(f21,plain,(
% 2.76/0.75    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.76/0.75    inference(ennf_transformation,[],[f10])).
% 2.76/0.75  fof(f10,axiom,(
% 2.76/0.75    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.76/0.75  fof(f41,plain,(
% 2.76/0.75    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f20])).
% 2.76/0.75  fof(f20,plain,(
% 2.76/0.75    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.76/0.75    inference(ennf_transformation,[],[f13])).
% 2.76/0.75  fof(f13,axiom,(
% 2.76/0.75    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.76/0.75  fof(f3227,plain,(
% 2.76/0.75    k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(sK2,sK0)) = k10_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 2.76/0.75    inference(forward_demodulation,[],[f3187,f40])).
% 2.76/0.75  fof(f3187,plain,(
% 2.76/0.75    k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k7_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k1_xboole_0))),
% 2.76/0.75    inference(superposition,[],[f1143,f70])).
% 2.76/0.75  fof(f70,plain,(
% 2.76/0.75    k1_xboole_0 = k4_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 2.76/0.75    inference(resolution,[],[f52,f38])).
% 2.76/0.75  fof(f38,plain,(
% 2.76/0.75    r1_tarski(k9_relat_1(sK2,sK0),sK1)),
% 2.76/0.75    inference(cnf_transformation,[],[f33])).
% 2.76/0.75  fof(f1143,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),X1)))) )),
% 2.76/0.75    inference(forward_demodulation,[],[f1141,f107])).
% 2.76/0.75  fof(f1141,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k10_relat_1(k7_relat_1(sK2,X0),k4_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),k4_xboole_0(k2_relat_1(k7_relat_1(sK2,X0)),X1)))) )),
% 2.76/0.75    inference(resolution,[],[f242,f35])).
% 2.76/0.75  fof(f242,plain,(
% 2.76/0.75    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k10_relat_1(k7_relat_1(X1,X2),X3) = k10_relat_1(k7_relat_1(X1,X2),k4_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),k4_xboole_0(k2_relat_1(k7_relat_1(X1,X2)),X3)))) )),
% 2.76/0.75    inference(resolution,[],[f61,f46])).
% 2.76/0.75  fof(f61,plain,(
% 2.76/0.75    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))) )),
% 2.76/0.75    inference(forward_demodulation,[],[f58,f57])).
% 2.76/0.75  fof(f57,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.76/0.75    inference(definition_unfolding,[],[f45,f56])).
% 2.76/0.75  fof(f56,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.76/0.75    inference(definition_unfolding,[],[f43,f44])).
% 2.76/0.75  fof(f44,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f8])).
% 2.76/0.75  fof(f8,axiom,(
% 2.76/0.75    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.76/0.75  fof(f43,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.76/0.75    inference(cnf_transformation,[],[f9])).
% 2.76/0.75  fof(f9,axiom,(
% 2.76/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.76/0.75  fof(f45,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f7])).
% 2.76/0.75  fof(f7,axiom,(
% 2.76/0.75    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.76/0.75  fof(f58,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 2.76/0.75    inference(definition_unfolding,[],[f48,f56])).
% 2.76/0.75  fof(f48,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f23])).
% 2.76/0.75  fof(f23,plain,(
% 2.76/0.75    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.76/0.75    inference(ennf_transformation,[],[f12])).
% 2.76/0.75  fof(f12,axiom,(
% 2.76/0.75    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 2.76/0.75  fof(f1744,plain,(
% 2.76/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k10_relat_1(sK2,X1)),k4_xboole_0(X0,k10_relat_1(k7_relat_1(sK2,X0),X1)))) )),
% 2.76/0.75    inference(superposition,[],[f659,f248])).
% 2.76/0.75  fof(f248,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK2,X1)))) )),
% 2.76/0.75    inference(resolution,[],[f62,f35])).
% 2.76/0.75  fof(f62,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1)))) )),
% 2.76/0.75    inference(forward_demodulation,[],[f59,f57])).
% 2.76/0.75  fof(f59,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 2.76/0.75    inference(definition_unfolding,[],[f53,f56])).
% 2.76/0.75  fof(f53,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f27])).
% 2.76/0.75  fof(f27,plain,(
% 2.76/0.75    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.76/0.75    inference(ennf_transformation,[],[f15])).
% 2.76/0.75  fof(f15,axiom,(
% 2.76/0.75    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 2.76/0.75  fof(f659,plain,(
% 2.76/0.75    ( ! [X24,X25] : (r1_tarski(k4_xboole_0(X24,X25),k4_xboole_0(X24,k4_xboole_0(X24,k4_xboole_0(X24,X25))))) )),
% 2.76/0.75    inference(resolution,[],[f209,f64])).
% 2.76/0.75  fof(f209,plain,(
% 2.76/0.75    ( ! [X6,X4,X5] : (~r1_tarski(k4_xboole_0(X4,X5),X6) | r1_tarski(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X4,X6)))) )),
% 2.76/0.75    inference(resolution,[],[f63,f42])).
% 2.76/0.75  fof(f63,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 2.76/0.75    inference(forward_demodulation,[],[f60,f57])).
% 2.76/0.75  fof(f60,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.76/0.75    inference(definition_unfolding,[],[f55,f56])).
% 2.76/0.75  fof(f55,plain,(
% 2.76/0.75    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f31])).
% 2.76/0.75  fof(f31,plain,(
% 2.76/0.75    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.76/0.75    inference(flattening,[],[f30])).
% 2.76/0.75  fof(f30,plain,(
% 2.76/0.75    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.76/0.75    inference(ennf_transformation,[],[f2])).
% 2.76/0.75  fof(f2,axiom,(
% 2.76/0.75    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.76/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.76/0.75  fof(f51,plain,(
% 2.76/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.76/0.75    inference(cnf_transformation,[],[f34])).
% 2.76/0.75  % SZS output end Proof for theBenchmark
% 2.76/0.75  % (14098)------------------------------
% 2.76/0.75  % (14098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.75  % (14098)Termination reason: Refutation
% 2.76/0.75  
% 2.76/0.75  % (14098)Memory used [KB]: 4477
% 2.76/0.75  % (14098)Time elapsed: 0.316 s
% 2.76/0.75  % (14098)------------------------------
% 2.76/0.75  % (14098)------------------------------
% 2.76/0.75  % (14096)Success in time 0.39 s
%------------------------------------------------------------------------------
