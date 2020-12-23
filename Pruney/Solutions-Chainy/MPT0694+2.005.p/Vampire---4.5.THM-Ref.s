%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 233 expanded)
%              Number of leaves         :   14 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  156 ( 521 expanded)
%              Number of equality atoms :   25 (  91 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(resolution,[],[f222,f125])).

fof(f125,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),k9_relat_1(sK2,X0)) ),
    inference(superposition,[],[f121,f86])).

fof(f86,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f50,f30])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f121,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k9_relat_1(sK2,X0)) ),
    inference(superposition,[],[f82,f66])).

fof(f66,plain,(
    ! [X4,X3] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X3,X3,X4))) = k9_relat_1(k7_relat_1(sK2,X3),k1_setfam_1(k1_enumset1(X3,X3,X4))) ),
    inference(resolution,[],[f63,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k9_relat_1(sK2,X0) = k9_relat_1(k7_relat_1(sK2,X1),X0) ) ),
    inference(resolution,[],[f33,f30])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0)) ),
    inference(resolution,[],[f81,f30])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f76,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X1))
      | r1_tarski(k9_relat_1(k7_relat_1(sK2,X1),X2),k9_relat_1(sK2,X1)) ) ),
    inference(backward_demodulation,[],[f58,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(resolution,[],[f56,f30])).

fof(f56,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3) ) ),
    inference(resolution,[],[f40,f38])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f58,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)),k9_relat_1(sK2,X1))
      | ~ v1_relat_1(k7_relat_1(sK2,X1)) ) ),
    inference(superposition,[],[f39,f55])).

fof(f55,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f40,f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(f222,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f198,f90])).

fof(f90,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
    | ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f88,f86])).

fof(f88,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) ),
    inference(backward_demodulation,[],[f77,f86])).

fof(f77,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f52,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) ),
    inference(backward_demodulation,[],[f47,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f36,f36])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f47,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f32,f46,f46])).

fof(f32,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f198,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) ),
    inference(resolution,[],[f197,f30])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) ) ),
    inference(resolution,[],[f196,f38])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(sK2,X0))
      | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) ) ),
    inference(resolution,[],[f195,f30])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1)
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f187,f31])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_relat_1(k7_relat_1(sK2,X0))
      | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f163,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f163,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(k7_relat_1(sK2,X2))
      | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3)),X3)
      | ~ v1_relat_1(k7_relat_1(sK2,X2)) ) ),
    inference(superposition,[],[f41,f96])).

fof(f96,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(resolution,[],[f95,f63])).

fof(f95,plain,(
    ! [X6,X5] : r1_tarski(k10_relat_1(k7_relat_1(sK2,X5),X6),X5) ),
    inference(superposition,[],[f48,f86])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:36:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (18389)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (18398)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (18399)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (18388)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (18394)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (18401)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (18403)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (18400)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (18395)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (18392)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (18390)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (18391)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (18389)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(resolution,[],[f222,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),k9_relat_1(sK2,X0))) )),
% 0.21/0.49    inference(superposition,[],[f121,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))) )),
% 0.21/0.49    inference(resolution,[],[f50,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f44,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f37,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k9_relat_1(sK2,X0))) )),
% 0.21/0.49    inference(superposition,[],[f82,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X4,X3] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X3,X3,X4))) = k9_relat_1(k7_relat_1(sK2,X3),k1_setfam_1(k1_enumset1(X3,X3,X4)))) )),
% 0.21/0.49    inference(resolution,[],[f63,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f34,f46])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(sK2,X0) = k9_relat_1(k7_relat_1(sK2,X1),X0)) )),
% 0.21/0.49    inference(resolution,[],[f33,f30])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0))) )),
% 0.21/0.49    inference(resolution,[],[f81,f30])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(k7_relat_1(sK2,X0),X1),k9_relat_1(sK2,X0))) )),
% 0.21/0.49    inference(resolution,[],[f76,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~v1_relat_1(k7_relat_1(sK2,X1)) | r1_tarski(k9_relat_1(k7_relat_1(sK2,X1),X2),k9_relat_1(sK2,X1))) )),
% 0.21/0.49    inference(backward_demodulation,[],[f58,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),X1)) )),
% 0.21/0.49    inference(resolution,[],[f56,f30])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)) )),
% 0.21/0.49    inference(resolution,[],[f40,f38])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)),k9_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X1))) )),
% 0.21/0.49    inference(superposition,[],[f39,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f40,f30])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0))),
% 0.21/0.49    inference(resolution,[],[f198,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) | ~r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f88,f86])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f77,f86])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)),
% 0.21/0.49    inference(resolution,[],[f52,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f45,f46])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))),
% 0.21/0.50    inference(backward_demodulation,[],[f47,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f35,f36,f36])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 0.21/0.50    inference(definition_unfolding,[],[f32,f46,f46])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1)) )),
% 0.21/0.50    inference(resolution,[],[f197,f30])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1)) )),
% 0.21/0.50    inference(resolution,[],[f196,f38])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK2,X0)) | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1)) )),
% 0.21/0.50    inference(resolution,[],[f195,f30])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.21/0.50    inference(resolution,[],[f187,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,X0)) | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)),X1) | ~v1_relat_1(sK2)) )),
% 0.21/0.50    inference(resolution,[],[f163,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~v1_funct_1(k7_relat_1(sK2,X2)) | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3)),X3) | ~v1_relat_1(k7_relat_1(sK2,X2))) )),
% 0.21/0.50    inference(superposition,[],[f41,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k9_relat_1(k7_relat_1(sK2,X0),k10_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 0.21/0.50    inference(resolution,[],[f95,f63])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X6,X5] : (r1_tarski(k10_relat_1(k7_relat_1(sK2,X5),X6),X5)) )),
% 0.21/0.50    inference(superposition,[],[f48,f86])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (18389)------------------------------
% 0.21/0.50  % (18389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18389)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (18389)Memory used [KB]: 1918
% 0.21/0.50  % (18389)Time elapsed: 0.059 s
% 0.21/0.50  % (18389)------------------------------
% 0.21/0.50  % (18389)------------------------------
% 0.21/0.50  % (18387)Success in time 0.131 s
%------------------------------------------------------------------------------
