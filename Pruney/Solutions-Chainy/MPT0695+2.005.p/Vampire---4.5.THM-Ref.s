%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:05 EST 2020

% Result     : Theorem 3.26s
% Output     : Refutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 214 expanded)
%              Number of leaves         :   14 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  143 ( 483 expanded)
%              Number of equality atoms :   60 ( 184 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7845,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f7786])).

fof(f7786,plain,(
    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f204,f7747])).

fof(f7747,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0))) ),
    inference(forward_demodulation,[],[f7712,f108])).

fof(f108,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0) ),
    inference(subsumption_resolution,[],[f102,f53])).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f38,f31])).

fof(f31,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f102,plain,(
    ! [X0] :
      ( k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    inference(resolution,[],[f39,f31])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f7712,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X0),X1)) ),
    inference(superposition,[],[f559,f670])).

fof(f670,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(sK2,X1))) ),
    inference(forward_demodulation,[],[f669,f93])).

fof(f93,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0) ),
    inference(backward_demodulation,[],[f78,f86])).

fof(f86,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f40,f31])).

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

fof(f78,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f34,f53])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f669,plain,(
    ! [X2,X1] : k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1))))) ),
    inference(subsumption_resolution,[],[f658,f53])).

fof(f658,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1)))))
      | ~ v1_relat_1(k7_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f50,f64])).

fof(f64,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK2,X0)) ),
    inference(subsumption_resolution,[],[f63,f31])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK2,X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f559,plain,(
    ! [X4,X2,X3] : k9_relat_1(k7_relat_1(sK2,X2),k10_relat_1(k7_relat_1(sK2,X3),X4)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2),X4)) ),
    inference(superposition,[],[f363,f196])).

fof(f196,plain,(
    ! [X4,X2,X3] : k10_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3),X4) = k1_setfam_1(k1_enumset1(X3,X3,k10_relat_1(k7_relat_1(sK2,X2),X4))) ),
    inference(resolution,[],[f51,f53])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f363,plain,(
    ! [X97,X98] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X97,X97,X98))) = k9_relat_1(k7_relat_1(sK2,X97),X98) ),
    inference(forward_demodulation,[],[f341,f87])).

fof(f87,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) = k9_relat_1(k7_relat_1(sK2,X1),X2) ),
    inference(resolution,[],[f40,f53])).

fof(f341,plain,(
    ! [X97,X98] : k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X97,X97,X98))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X97),X98)) ),
    inference(superposition,[],[f86,f303])).

fof(f303,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(resolution,[],[f52,f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f204,plain,(
    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(backward_demodulation,[],[f181,f195])).

fof(f195,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f51,f31])).

fof(f181,plain,(
    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(forward_demodulation,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f35,f36,f36])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f48,plain,(
    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) ),
    inference(definition_unfolding,[],[f33,f47,f47])).

fof(f33,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:49:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (32590)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (32589)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (32591)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (32588)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (32592)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (32598)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (32597)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (32599)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (32587)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (32596)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (32585)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (32586)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (32601)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (32594)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (32595)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (32600)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (32602)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (32593)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 3.26/0.80  % (32597)Refutation found. Thanks to Tanya!
% 3.26/0.80  % SZS status Theorem for theBenchmark
% 3.26/0.80  % SZS output start Proof for theBenchmark
% 3.26/0.80  fof(f7845,plain,(
% 3.26/0.80    $false),
% 3.26/0.80    inference(trivial_inequality_removal,[],[f7786])).
% 3.26/0.80  fof(f7786,plain,(
% 3.26/0.80    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),
% 3.26/0.80    inference(superposition,[],[f204,f7747])).
% 3.26/0.80  fof(f7747,plain,(
% 3.26/0.80    ( ! [X0,X1] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0),X1)) = k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0)))) )),
% 3.26/0.80    inference(forward_demodulation,[],[f7712,f108])).
% 3.26/0.80  fof(f108,plain,(
% 3.26/0.80    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)) )),
% 3.26/0.80    inference(subsumption_resolution,[],[f102,f53])).
% 3.26/0.80  fof(f53,plain,(
% 3.26/0.80    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 3.26/0.80    inference(resolution,[],[f38,f31])).
% 3.26/0.80  fof(f31,plain,(
% 3.26/0.80    v1_relat_1(sK2)),
% 3.26/0.80    inference(cnf_transformation,[],[f30])).
% 3.26/0.80  fof(f30,plain,(
% 3.26/0.80    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.26/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f29])).
% 3.26/0.80  fof(f29,plain,(
% 3.26/0.80    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.26/0.80    introduced(choice_axiom,[])).
% 3.26/0.80  fof(f16,plain,(
% 3.26/0.80    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.26/0.80    inference(flattening,[],[f15])).
% 3.26/0.80  fof(f15,plain,(
% 3.26/0.80    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.26/0.80    inference(ennf_transformation,[],[f14])).
% 3.26/0.80  fof(f14,negated_conjecture,(
% 3.26/0.80    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 3.26/0.80    inference(negated_conjecture,[],[f13])).
% 3.26/0.80  fof(f13,conjecture,(
% 3.26/0.80    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).
% 3.26/0.80  fof(f38,plain,(
% 3.26/0.80    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 3.26/0.80    inference(cnf_transformation,[],[f18])).
% 3.26/0.80  fof(f18,plain,(
% 3.26/0.80    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.26/0.80    inference(ennf_transformation,[],[f4])).
% 3.26/0.80  fof(f4,axiom,(
% 3.26/0.80    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 3.26/0.80  fof(f102,plain,(
% 3.26/0.80    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 3.26/0.80    inference(resolution,[],[f41,f58])).
% 3.26/0.80  fof(f58,plain,(
% 3.26/0.80    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) )),
% 3.26/0.80    inference(resolution,[],[f39,f31])).
% 3.26/0.80  fof(f39,plain,(
% 3.26/0.80    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f19])).
% 3.26/0.80  fof(f19,plain,(
% 3.26/0.80    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.26/0.80    inference(ennf_transformation,[],[f8])).
% 3.26/0.80  fof(f8,axiom,(
% 3.26/0.80    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 3.26/0.80  fof(f41,plain,(
% 3.26/0.80    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f22])).
% 3.26/0.80  fof(f22,plain,(
% 3.26/0.80    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.26/0.80    inference(flattening,[],[f21])).
% 3.26/0.80  fof(f21,plain,(
% 3.26/0.80    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.26/0.80    inference(ennf_transformation,[],[f9])).
% 3.26/0.80  fof(f9,axiom,(
% 3.26/0.80    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 3.26/0.80  fof(f7712,plain,(
% 3.26/0.80    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(sK2,X0))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X0),X1))) )),
% 3.26/0.80    inference(superposition,[],[f559,f670])).
% 3.26/0.80  fof(f670,plain,(
% 3.26/0.80    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(sK2,X1)))) )),
% 3.26/0.80    inference(forward_demodulation,[],[f669,f93])).
% 3.26/0.80  fof(f93,plain,(
% 3.26/0.80    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,X0)) )),
% 3.26/0.80    inference(backward_demodulation,[],[f78,f86])).
% 3.26/0.80  fof(f86,plain,(
% 3.26/0.80    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 3.26/0.80    inference(resolution,[],[f40,f31])).
% 3.26/0.80  fof(f40,plain,(
% 3.26/0.80    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f20])).
% 3.26/0.80  fof(f20,plain,(
% 3.26/0.80    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.26/0.80    inference(ennf_transformation,[],[f7])).
% 3.26/0.80  fof(f7,axiom,(
% 3.26/0.80    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 3.26/0.80  fof(f78,plain,(
% 3.26/0.80    ( ! [X0] : (k9_relat_1(k7_relat_1(sK2,X0),k1_relat_1(k7_relat_1(sK2,X0))) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 3.26/0.80    inference(resolution,[],[f34,f53])).
% 3.26/0.80  fof(f34,plain,(
% 3.26/0.80    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f17])).
% 3.26/0.80  fof(f17,plain,(
% 3.26/0.80    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.26/0.80    inference(ennf_transformation,[],[f6])).
% 3.26/0.80  fof(f6,axiom,(
% 3.26/0.80    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 3.26/0.80  fof(f669,plain,(
% 3.26/0.80    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1)))))) )),
% 3.26/0.80    inference(subsumption_resolution,[],[f658,f53])).
% 3.26/0.80  fof(f658,plain,(
% 3.26/0.80    ( ! [X2,X1] : (k9_relat_1(k7_relat_1(sK2,X1),k10_relat_1(k7_relat_1(sK2,X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1))))) | ~v1_relat_1(k7_relat_1(sK2,X1))) )),
% 3.26/0.80    inference(resolution,[],[f50,f64])).
% 3.26/0.80  fof(f64,plain,(
% 3.26/0.80    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0))) )),
% 3.26/0.80    inference(subsumption_resolution,[],[f63,f31])).
% 3.26/0.80  fof(f63,plain,(
% 3.26/0.80    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(sK2)) )),
% 3.26/0.80    inference(resolution,[],[f44,f32])).
% 3.26/0.80  fof(f32,plain,(
% 3.26/0.80    v1_funct_1(sK2)),
% 3.26/0.80    inference(cnf_transformation,[],[f30])).
% 3.26/0.80  fof(f44,plain,(
% 3.26/0.80    ( ! [X0,X1] : (~v1_funct_1(X0) | v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f26])).
% 3.26/0.80  fof(f26,plain,(
% 3.26/0.80    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.26/0.80    inference(flattening,[],[f25])).
% 3.26/0.80  fof(f25,plain,(
% 3.26/0.80    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.26/0.80    inference(ennf_transformation,[],[f10])).
% 3.26/0.80  fof(f10,axiom,(
% 3.26/0.80    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 3.26/0.80  fof(f50,plain,(
% 3.26/0.80    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 3.26/0.80    inference(definition_unfolding,[],[f42,f47])).
% 3.26/0.80  fof(f47,plain,(
% 3.26/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.26/0.80    inference(definition_unfolding,[],[f37,f36])).
% 3.26/0.80  fof(f36,plain,(
% 3.26/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f2])).
% 3.26/0.80  fof(f2,axiom,(
% 3.26/0.80    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.26/0.80  fof(f37,plain,(
% 3.26/0.80    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f3])).
% 3.26/0.80  fof(f3,axiom,(
% 3.26/0.80    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.26/0.80  fof(f42,plain,(
% 3.26/0.80    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f24])).
% 3.26/0.80  fof(f24,plain,(
% 3.26/0.80    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.26/0.80    inference(flattening,[],[f23])).
% 3.26/0.80  fof(f23,plain,(
% 3.26/0.80    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.26/0.80    inference(ennf_transformation,[],[f12])).
% 3.26/0.80  fof(f12,axiom,(
% 3.26/0.80    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 3.26/0.80  fof(f559,plain,(
% 3.26/0.80    ( ! [X4,X2,X3] : (k9_relat_1(k7_relat_1(sK2,X2),k10_relat_1(k7_relat_1(sK2,X3),X4)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2),X4))) )),
% 3.26/0.80    inference(superposition,[],[f363,f196])).
% 3.26/0.80  fof(f196,plain,(
% 3.26/0.80    ( ! [X4,X2,X3] : (k10_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3),X4) = k1_setfam_1(k1_enumset1(X3,X3,k10_relat_1(k7_relat_1(sK2,X2),X4)))) )),
% 3.26/0.80    inference(resolution,[],[f51,f53])).
% 3.26/0.80  fof(f51,plain,(
% 3.26/0.80    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 3.26/0.80    inference(definition_unfolding,[],[f45,f47])).
% 3.26/0.80  fof(f45,plain,(
% 3.26/0.80    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f27])).
% 3.26/0.80  fof(f27,plain,(
% 3.26/0.80    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.26/0.80    inference(ennf_transformation,[],[f11])).
% 3.26/0.80  fof(f11,axiom,(
% 3.26/0.80    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 3.26/0.80  fof(f363,plain,(
% 3.26/0.80    ( ! [X97,X98] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X97,X97,X98))) = k9_relat_1(k7_relat_1(sK2,X97),X98)) )),
% 3.26/0.80    inference(forward_demodulation,[],[f341,f87])).
% 3.26/0.80  fof(f87,plain,(
% 3.26/0.80    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) = k9_relat_1(k7_relat_1(sK2,X1),X2)) )),
% 3.26/0.80    inference(resolution,[],[f40,f53])).
% 3.26/0.80  fof(f341,plain,(
% 3.26/0.80    ( ! [X97,X98] : (k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X97,X97,X98))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X97),X98))) )),
% 3.26/0.80    inference(superposition,[],[f86,f303])).
% 3.26/0.80  fof(f303,plain,(
% 3.26/0.80    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.26/0.80    inference(resolution,[],[f52,f31])).
% 3.26/0.80  fof(f52,plain,(
% 3.26/0.80    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.26/0.80    inference(definition_unfolding,[],[f46,f47])).
% 3.26/0.80  fof(f46,plain,(
% 3.26/0.80    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f28])).
% 3.26/0.80  fof(f28,plain,(
% 3.26/0.80    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.26/0.80    inference(ennf_transformation,[],[f5])).
% 3.26/0.80  fof(f5,axiom,(
% 3.26/0.80    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 3.26/0.80  fof(f204,plain,(
% 3.26/0.80    k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 3.26/0.80    inference(backward_demodulation,[],[f181,f195])).
% 3.26/0.80  fof(f195,plain,(
% 3.26/0.80    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1)))) )),
% 3.26/0.80    inference(resolution,[],[f51,f31])).
% 3.26/0.80  fof(f181,plain,(
% 3.26/0.80    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))),
% 3.26/0.80    inference(forward_demodulation,[],[f48,f49])).
% 3.26/0.80  fof(f49,plain,(
% 3.26/0.80    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.26/0.80    inference(definition_unfolding,[],[f35,f36,f36])).
% 3.26/0.80  fof(f35,plain,(
% 3.26/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.26/0.80    inference(cnf_transformation,[],[f1])).
% 3.26/0.80  fof(f1,axiom,(
% 3.26/0.80    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.26/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.26/0.80  fof(f48,plain,(
% 3.26/0.80    k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))),
% 3.26/0.80    inference(definition_unfolding,[],[f33,f47,f47])).
% 3.26/0.80  fof(f33,plain,(
% 3.26/0.80    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 3.26/0.80    inference(cnf_transformation,[],[f30])).
% 3.26/0.80  % SZS output end Proof for theBenchmark
% 3.26/0.80  % (32597)------------------------------
% 3.26/0.80  % (32597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.80  % (32597)Termination reason: Refutation
% 3.26/0.80  
% 3.26/0.80  % (32597)Memory used [KB]: 6780
% 3.26/0.80  % (32597)Time elapsed: 0.370 s
% 3.26/0.80  % (32597)------------------------------
% 3.26/0.80  % (32597)------------------------------
% 3.26/0.80  % (32584)Success in time 0.44 s
%------------------------------------------------------------------------------
