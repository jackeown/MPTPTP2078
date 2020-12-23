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
% DateTime   : Thu Dec  3 12:53:46 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 246 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   19
%              Number of atoms          :  161 ( 538 expanded)
%              Number of equality atoms :   58 ( 138 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2051,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2039,f37])).

fof(f37,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f2039,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f355,f2017])).

fof(f2017,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2016,f774])).

fof(f774,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f283,f179])).

fof(f179,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f176,f96])).

fof(f96,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f89,f62])).

fof(f62,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f89,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f44,f62])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f176,plain,(
    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f56,f164])).

fof(f164,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f149,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f51,f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f149,plain,(
    ! [X5] : r1_tarski(k4_xboole_0(sK0,k1_relat_1(sK1)),X5) ),
    inference(resolution,[],[f54,f77])).

fof(f77,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f75,f65])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f55,f64])).

fof(f64,plain,(
    k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f283,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f198,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f198,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f57,f35])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f2016,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f604,f2012])).

fof(f2012,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2008,f369])).

fof(f369,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0) ),
    inference(resolution,[],[f212,f35])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X1),X1) ) ),
    inference(resolution,[],[f41,f60])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f2008,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f646,f774])).

fof(f646,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f79,f35])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f604,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f73,f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f39,f46])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f355,plain,(
    ! [X4,X5] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X4),X5),k10_relat_1(sK1,X5)) ),
    inference(superposition,[],[f134,f226])).

fof(f226,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f58,f35])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f52,f43])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f134,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f127,f42])).

fof(f127,plain,(
    ! [X2,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(resolution,[],[f59,f60])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f43])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (28473)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (28462)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (28461)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (28471)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (28459)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (28478)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (28480)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (28460)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (28470)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (28472)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (28466)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (28486)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.53  % (28458)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.53  % (28484)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.53  % (28463)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.53  % (28481)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.53  % (28464)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.53  % (28487)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (28474)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.54  % (28476)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.54  % (28465)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.54  % (28469)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.54  % (28467)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.54  % (28486)Refutation not found, incomplete strategy% (28486)------------------------------
% 1.34/0.54  % (28486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (28486)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (28486)Memory used [KB]: 10746
% 1.34/0.54  % (28486)Time elapsed: 0.127 s
% 1.34/0.54  % (28486)------------------------------
% 1.34/0.54  % (28486)------------------------------
% 1.50/0.55  % (28479)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.55  % (28474)Refutation not found, incomplete strategy% (28474)------------------------------
% 1.50/0.55  % (28474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (28474)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (28474)Memory used [KB]: 10618
% 1.50/0.55  % (28474)Time elapsed: 0.135 s
% 1.50/0.55  % (28474)------------------------------
% 1.50/0.55  % (28474)------------------------------
% 1.50/0.55  % (28483)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.50/0.55  % (28485)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.55  % (28482)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.50/0.55  % (28468)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.55  % (28468)Refutation not found, incomplete strategy% (28468)------------------------------
% 1.50/0.55  % (28468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (28477)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.50/0.56  % (28475)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.56  % (28468)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (28468)Memory used [KB]: 10746
% 1.50/0.56  % (28468)Time elapsed: 0.151 s
% 1.50/0.56  % (28468)------------------------------
% 1.50/0.56  % (28468)------------------------------
% 2.04/0.64  % (28464)Refutation found. Thanks to Tanya!
% 2.04/0.64  % SZS status Theorem for theBenchmark
% 2.04/0.64  % SZS output start Proof for theBenchmark
% 2.04/0.64  fof(f2051,plain,(
% 2.04/0.64    $false),
% 2.04/0.64    inference(subsumption_resolution,[],[f2039,f37])).
% 2.04/0.64  fof(f37,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.04/0.64    inference(cnf_transformation,[],[f32])).
% 2.04/0.64  fof(f32,plain,(
% 2.04/0.64    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 2.04/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).
% 2.04/0.64  fof(f31,plain,(
% 2.04/0.64    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 2.04/0.64    introduced(choice_axiom,[])).
% 2.04/0.64  fof(f20,plain,(
% 2.04/0.64    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 2.04/0.64    inference(flattening,[],[f19])).
% 2.04/0.64  fof(f19,plain,(
% 2.04/0.64    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.04/0.64    inference(ennf_transformation,[],[f18])).
% 2.04/0.64  fof(f18,negated_conjecture,(
% 2.04/0.64    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.04/0.64    inference(negated_conjecture,[],[f17])).
% 2.04/0.64  fof(f17,conjecture,(
% 2.04/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 2.04/0.64  fof(f2039,plain,(
% 2.04/0.64    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.04/0.64    inference(superposition,[],[f355,f2017])).
% 2.04/0.64  fof(f2017,plain,(
% 2.04/0.64    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 2.04/0.64    inference(forward_demodulation,[],[f2016,f774])).
% 2.04/0.64  fof(f774,plain,(
% 2.04/0.64    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 2.04/0.64    inference(superposition,[],[f283,f179])).
% 2.04/0.64  fof(f179,plain,(
% 2.04/0.64    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 2.04/0.64    inference(forward_demodulation,[],[f176,f96])).
% 2.04/0.64  fof(f96,plain,(
% 2.04/0.64    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.04/0.64    inference(forward_demodulation,[],[f89,f62])).
% 2.04/0.64  fof(f62,plain,(
% 2.04/0.64    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.04/0.64    inference(resolution,[],[f48,f38])).
% 2.04/0.64  fof(f38,plain,(
% 2.04/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f5])).
% 2.04/0.64  fof(f5,axiom,(
% 2.04/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.04/0.64  fof(f48,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.04/0.64    inference(cnf_transformation,[],[f26])).
% 2.04/0.64  fof(f26,plain,(
% 2.04/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.04/0.64    inference(ennf_transformation,[],[f3])).
% 2.04/0.64  fof(f3,axiom,(
% 2.04/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.04/0.64  fof(f89,plain,(
% 2.04/0.64    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X2)) )),
% 2.04/0.64    inference(superposition,[],[f44,f62])).
% 2.04/0.64  fof(f44,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f6])).
% 2.04/0.64  fof(f6,axiom,(
% 2.04/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.04/0.64  fof(f176,plain,(
% 2.04/0.64    k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k4_xboole_0(sK0,k1_xboole_0)),
% 2.04/0.64    inference(superposition,[],[f56,f164])).
% 2.04/0.64  fof(f164,plain,(
% 2.04/0.64    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 2.04/0.64    inference(resolution,[],[f149,f103])).
% 2.04/0.64  fof(f103,plain,(
% 2.04/0.64    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.04/0.64    inference(resolution,[],[f51,f38])).
% 2.04/0.64  fof(f51,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f34])).
% 2.04/0.64  fof(f34,plain,(
% 2.04/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.64    inference(flattening,[],[f33])).
% 2.04/0.64  fof(f33,plain,(
% 2.04/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.04/0.64    inference(nnf_transformation,[],[f1])).
% 2.04/0.64  fof(f1,axiom,(
% 2.04/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.04/0.64  fof(f149,plain,(
% 2.04/0.64    ( ! [X5] : (r1_tarski(k4_xboole_0(sK0,k1_relat_1(sK1)),X5)) )),
% 2.04/0.64    inference(resolution,[],[f54,f77])).
% 2.04/0.64  fof(f77,plain,(
% 2.04/0.64    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(k1_relat_1(sK1),X0))) )),
% 2.04/0.64    inference(resolution,[],[f75,f65])).
% 2.04/0.64  fof(f65,plain,(
% 2.04/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.04/0.64    inference(resolution,[],[f55,f60])).
% 2.04/0.64  fof(f60,plain,(
% 2.04/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.04/0.64    inference(equality_resolution,[],[f50])).
% 2.04/0.64  fof(f50,plain,(
% 2.04/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.04/0.64    inference(cnf_transformation,[],[f34])).
% 2.04/0.64  fof(f55,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f30])).
% 2.04/0.64  fof(f30,plain,(
% 2.04/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.04/0.64    inference(ennf_transformation,[],[f2])).
% 2.04/0.64  fof(f2,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.04/0.64  fof(f75,plain,(
% 2.04/0.64    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | r1_tarski(sK0,X0)) )),
% 2.04/0.64    inference(superposition,[],[f55,f64])).
% 2.04/0.64  fof(f64,plain,(
% 2.04/0.64    k1_relat_1(sK1) = k2_xboole_0(sK0,k1_relat_1(sK1))),
% 2.04/0.64    inference(resolution,[],[f48,f36])).
% 2.04/0.64  fof(f36,plain,(
% 2.04/0.64    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.04/0.64    inference(cnf_transformation,[],[f32])).
% 2.04/0.64  fof(f54,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f29])).
% 2.04/0.64  fof(f29,plain,(
% 2.04/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.04/0.64    inference(ennf_transformation,[],[f7])).
% 2.04/0.64  fof(f7,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.04/0.64  fof(f56,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.04/0.64    inference(definition_unfolding,[],[f45,f43])).
% 2.04/0.64  fof(f43,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f10])).
% 2.04/0.64  fof(f10,axiom,(
% 2.04/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.04/0.64  fof(f45,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f8])).
% 2.04/0.64  fof(f8,axiom,(
% 2.04/0.64    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.04/0.64  fof(f283,plain,(
% 2.04/0.64    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 2.04/0.64    inference(superposition,[],[f198,f42])).
% 2.04/0.64  fof(f42,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f9])).
% 2.04/0.64  fof(f9,axiom,(
% 2.04/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.04/0.64  fof(f198,plain,(
% 2.04/0.64    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 2.04/0.64    inference(resolution,[],[f57,f35])).
% 2.04/0.64  fof(f35,plain,(
% 2.04/0.64    v1_relat_1(sK1)),
% 2.04/0.64    inference(cnf_transformation,[],[f32])).
% 2.04/0.64  fof(f57,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 2.04/0.64    inference(definition_unfolding,[],[f47,f43])).
% 2.04/0.64  fof(f47,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f25])).
% 2.04/0.64  fof(f25,plain,(
% 2.04/0.64    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.04/0.64    inference(ennf_transformation,[],[f15])).
% 2.04/0.64  fof(f15,axiom,(
% 2.04/0.64    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 2.04/0.64  fof(f2016,plain,(
% 2.04/0.64    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 2.04/0.64    inference(superposition,[],[f604,f2012])).
% 2.04/0.64  fof(f2012,plain,(
% 2.04/0.64    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 2.04/0.64    inference(forward_demodulation,[],[f2008,f369])).
% 2.04/0.64  fof(f369,plain,(
% 2.04/0.64    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(k7_relat_1(sK1,X0),X0)) )),
% 2.04/0.64    inference(resolution,[],[f212,f35])).
% 2.04/0.64  fof(f212,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X1),X1)) )),
% 2.04/0.64    inference(resolution,[],[f41,f60])).
% 2.04/0.64  fof(f41,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f23])).
% 2.04/0.64  fof(f23,plain,(
% 2.04/0.64    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.04/0.64    inference(ennf_transformation,[],[f13])).
% 2.04/0.64  fof(f13,axiom,(
% 2.04/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 2.04/0.64  fof(f2008,plain,(
% 2.04/0.64    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 2.04/0.64    inference(superposition,[],[f646,f774])).
% 2.04/0.64  fof(f646,plain,(
% 2.04/0.64    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.04/0.64    inference(resolution,[],[f79,f35])).
% 2.04/0.64  fof(f79,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1)))) )),
% 2.04/0.64    inference(resolution,[],[f40,f46])).
% 2.04/0.64  fof(f46,plain,(
% 2.04/0.64    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f24])).
% 2.04/0.64  fof(f24,plain,(
% 2.04/0.64    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.04/0.64    inference(ennf_transformation,[],[f11])).
% 2.04/0.64  fof(f11,axiom,(
% 2.04/0.64    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.04/0.64  fof(f40,plain,(
% 2.04/0.64    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f22])).
% 2.04/0.64  fof(f22,plain,(
% 2.04/0.64    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.04/0.64    inference(ennf_transformation,[],[f12])).
% 2.04/0.64  fof(f12,axiom,(
% 2.04/0.64    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 2.04/0.64  fof(f604,plain,(
% 2.04/0.64    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.04/0.64    inference(resolution,[],[f73,f35])).
% 2.04/0.64  fof(f73,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1)))) )),
% 2.04/0.64    inference(resolution,[],[f39,f46])).
% 2.04/0.64  fof(f39,plain,(
% 2.04/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f21])).
% 2.04/0.64  fof(f21,plain,(
% 2.04/0.64    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.04/0.64    inference(ennf_transformation,[],[f14])).
% 2.04/0.64  fof(f14,axiom,(
% 2.04/0.64    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.04/0.64  fof(f355,plain,(
% 2.04/0.64    ( ! [X4,X5] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X4),X5),k10_relat_1(sK1,X5))) )),
% 2.04/0.64    inference(superposition,[],[f134,f226])).
% 2.04/0.64  fof(f226,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))) )),
% 2.04/0.64    inference(resolution,[],[f58,f35])).
% 2.04/0.64  fof(f58,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 2.04/0.64    inference(definition_unfolding,[],[f52,f43])).
% 2.04/0.64  fof(f52,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f27])).
% 2.04/0.64  fof(f27,plain,(
% 2.04/0.64    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.04/0.64    inference(ennf_transformation,[],[f16])).
% 2.04/0.64  fof(f16,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 2.04/0.64  fof(f134,plain,(
% 2.04/0.64    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 2.04/0.64    inference(superposition,[],[f127,f42])).
% 2.04/0.64  fof(f127,plain,(
% 2.04/0.64    ( ! [X2,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)) )),
% 2.04/0.64    inference(resolution,[],[f59,f60])).
% 2.04/0.64  fof(f59,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | r1_tarski(X0,X1)) )),
% 2.04/0.64    inference(definition_unfolding,[],[f53,f43])).
% 2.04/0.64  fof(f53,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f28])).
% 2.04/0.64  fof(f28,plain,(
% 2.04/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.04/0.64    inference(ennf_transformation,[],[f4])).
% 2.04/0.64  fof(f4,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 2.04/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 2.04/0.64  % SZS output end Proof for theBenchmark
% 2.04/0.64  % (28464)------------------------------
% 2.04/0.64  % (28464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.64  % (28464)Termination reason: Refutation
% 2.04/0.64  
% 2.04/0.64  % (28464)Memory used [KB]: 12153
% 2.04/0.64  % (28464)Time elapsed: 0.197 s
% 2.04/0.64  % (28464)------------------------------
% 2.04/0.64  % (28464)------------------------------
% 2.04/0.64  % (28457)Success in time 0.281 s
%------------------------------------------------------------------------------
