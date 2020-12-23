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
% DateTime   : Thu Dec  3 12:53:50 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 205 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  165 ( 409 expanded)
%              Number of equality atoms :   76 ( 113 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2316,plain,(
    $false ),
    inference(resolution,[],[f2313,f41])).

fof(f41,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f2313,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f2312,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f2312,plain,(
    r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f2311,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f2311,plain,(
    r1_tarski(k5_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f2296,f143])).

fof(f143,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f64,f54])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f64,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2296,plain,(
    r1_tarski(k5_xboole_0(k1_relat_1(sK1),k5_xboole_0(sK0,k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f2199,f345])).

fof(f345,plain,(
    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(forward_demodulation,[],[f339,f44])).

fof(f339,plain,(
    k2_xboole_0(k1_relat_1(sK1),sK0) = k5_xboole_0(k1_relat_1(sK1),k1_xboole_0) ),
    inference(superposition,[],[f150,f334])).

fof(f334,plain,(
    k1_xboole_0 = k5_xboole_0(k1_relat_1(sK1),k2_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f329,f43])).

fof(f329,plain,(
    k5_xboole_0(k1_relat_1(sK1),k2_xboole_0(sK0,k1_relat_1(sK1))) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f149,f245])).

fof(f245,plain,(
    sK0 = k5_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k2_xboole_0(sK0,k1_relat_1(sK1)))) ),
    inference(resolution,[],[f69,f40])).

fof(f40,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) = X0 ) ),
    inference(backward_demodulation,[],[f68,f64])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f149,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f135,f79])).

fof(f79,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f54,f44])).

fof(f135,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f64,f43])).

fof(f150,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f70,f149])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k2_xboole_0(X1,X0))))) ),
    inference(backward_demodulation,[],[f66,f64])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f2199,plain,(
    ! [X7] : r1_tarski(k5_xboole_0(k1_relat_1(sK1),k5_xboole_0(X7,k2_xboole_0(k1_relat_1(sK1),X7))),k10_relat_1(sK1,k9_relat_1(sK1,X7))) ),
    inference(backward_demodulation,[],[f381,f2198])).

fof(f2198,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k9_relat_1(k4_relat_1(sK1),X7) ),
    inference(forward_demodulation,[],[f2195,f2185])).

fof(f2185,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) ),
    inference(backward_demodulation,[],[f964,f2184])).

fof(f2184,plain,(
    ! [X1] : k4_relat_1(k8_relat_1(X1,sK1)) = k7_relat_1(k4_relat_1(sK1),X1) ),
    inference(backward_demodulation,[],[f377,f2181])).

fof(f2181,plain,(
    ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1)) ),
    inference(resolution,[],[f109,f39])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(resolution,[],[f60,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f377,plain,(
    ! [X1] : k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X1,sK1)) ),
    inference(forward_demodulation,[],[f376,f102])).

fof(f102,plain,(
    ! [X7] : k8_relat_1(X7,sK1) = k5_relat_1(sK1,k6_relat_1(X7)) ),
    inference(resolution,[],[f59,f39])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f376,plain,(
    ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f373,f45])).

fof(f45,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f373,plain,(
    ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(sK1)) ),
    inference(resolution,[],[f362,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f362,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)) ) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f964,plain,(
    ! [X7] : k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1))) = k10_relat_1(sK1,X7) ),
    inference(forward_demodulation,[],[f963,f371])).

fof(f371,plain,(
    ! [X1] : k10_relat_1(sK1,X1) = k1_relat_1(k8_relat_1(X1,sK1)) ),
    inference(forward_demodulation,[],[f370,f102])).

fof(f370,plain,(
    ! [X1] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k10_relat_1(sK1,X1) ),
    inference(forward_demodulation,[],[f367,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f367,plain,(
    ! [X1] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X1))) ),
    inference(resolution,[],[f299,f42])).

fof(f299,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k1_relat_1(k5_relat_1(sK1,X7)) = k10_relat_1(sK1,k1_relat_1(X7)) ) ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f963,plain,(
    ! [X7] : k1_relat_1(k8_relat_1(X7,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1))) ),
    inference(resolution,[],[f95,f39])).

fof(f95,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k8_relat_1(X2,X3)) = k2_relat_1(k4_relat_1(k8_relat_1(X2,X3))) ) ),
    inference(resolution,[],[f51,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f2195,plain,(
    ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7) ),
    inference(resolution,[],[f114,f39])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1) ) ),
    inference(resolution,[],[f61,f48])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f381,plain,(
    ! [X7] : r1_tarski(k5_xboole_0(k1_relat_1(sK1),k5_xboole_0(X7,k2_xboole_0(k1_relat_1(sK1),X7))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X7))) ),
    inference(resolution,[],[f71,f39])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_xboole_0(k1_relat_1(X1),k5_xboole_0(X0,k2_xboole_0(k1_relat_1(X1),X0))),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    inference(backward_demodulation,[],[f67,f64])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(X1),X0),k2_xboole_0(k1_relat_1(X1),X0)),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f62,f57])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:04:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (29742)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (29746)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (29747)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (29754)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (29755)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (29757)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (29756)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (29744)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (29749)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (29745)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (29751)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (29741)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (29752)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (29758)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (29743)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (29748)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (29753)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (29750)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.49/0.55  % (29742)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.55  % SZS output start Proof for theBenchmark
% 1.49/0.55  fof(f2316,plain,(
% 1.49/0.55    $false),
% 1.49/0.55    inference(resolution,[],[f2313,f41])).
% 1.49/0.55  fof(f41,plain,(
% 1.49/0.55    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.49/0.55    inference(cnf_transformation,[],[f38])).
% 1.49/0.55  fof(f38,plain,(
% 1.49/0.55    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f37])).
% 1.49/0.55  fof(f37,plain,(
% 1.49/0.55    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f25,plain,(
% 1.49/0.55    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.49/0.55    inference(flattening,[],[f24])).
% 1.49/0.55  fof(f24,plain,(
% 1.49/0.55    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f23])).
% 1.49/0.55  fof(f23,negated_conjecture,(
% 1.49/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.49/0.55    inference(negated_conjecture,[],[f22])).
% 1.49/0.55  fof(f22,conjecture,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.49/0.55  fof(f2313,plain,(
% 1.49/0.55    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.49/0.55    inference(forward_demodulation,[],[f2312,f44])).
% 1.49/0.55  fof(f44,plain,(
% 1.49/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f4])).
% 1.49/0.55  fof(f4,axiom,(
% 1.49/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.49/0.55  fof(f2312,plain,(
% 1.49/0.55    r1_tarski(k5_xboole_0(sK0,k1_xboole_0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.49/0.55    inference(forward_demodulation,[],[f2311,f43])).
% 1.49/0.55  fof(f43,plain,(
% 1.49/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f6])).
% 1.49/0.55  fof(f6,axiom,(
% 1.49/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.49/0.55  fof(f2311,plain,(
% 1.49/0.55    r1_tarski(k5_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.49/0.55    inference(forward_demodulation,[],[f2296,f143])).
% 1.49/0.55  fof(f143,plain,(
% 1.49/0.55    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 1.49/0.55    inference(superposition,[],[f64,f54])).
% 1.49/0.55  fof(f54,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f1])).
% 1.49/0.55  fof(f1,axiom,(
% 1.49/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.49/0.55  fof(f64,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f5])).
% 1.49/0.55  fof(f5,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.49/0.55  fof(f2296,plain,(
% 1.49/0.55    r1_tarski(k5_xboole_0(k1_relat_1(sK1),k5_xboole_0(sK0,k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.49/0.55    inference(superposition,[],[f2199,f345])).
% 1.49/0.55  fof(f345,plain,(
% 1.49/0.55    k1_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),sK0)),
% 1.49/0.55    inference(forward_demodulation,[],[f339,f44])).
% 1.49/0.55  fof(f339,plain,(
% 1.49/0.55    k2_xboole_0(k1_relat_1(sK1),sK0) = k5_xboole_0(k1_relat_1(sK1),k1_xboole_0)),
% 1.49/0.55    inference(superposition,[],[f150,f334])).
% 1.49/0.55  fof(f334,plain,(
% 1.49/0.55    k1_xboole_0 = k5_xboole_0(k1_relat_1(sK1),k2_xboole_0(sK0,k1_relat_1(sK1)))),
% 1.49/0.55    inference(forward_demodulation,[],[f329,f43])).
% 1.49/0.55  fof(f329,plain,(
% 1.49/0.55    k5_xboole_0(k1_relat_1(sK1),k2_xboole_0(sK0,k1_relat_1(sK1))) = k5_xboole_0(sK0,sK0)),
% 1.49/0.55    inference(superposition,[],[f149,f245])).
% 1.49/0.55  fof(f245,plain,(
% 1.49/0.55    sK0 = k5_xboole_0(sK0,k5_xboole_0(k1_relat_1(sK1),k2_xboole_0(sK0,k1_relat_1(sK1))))),
% 1.49/0.55    inference(resolution,[],[f69,f40])).
% 1.49/0.55  fof(f40,plain,(
% 1.49/0.55    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.49/0.55    inference(cnf_transformation,[],[f38])).
% 1.49/0.55  fof(f69,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) = X0) )),
% 1.49/0.55    inference(backward_demodulation,[],[f68,f64])).
% 1.49/0.55  fof(f68,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.55    inference(definition_unfolding,[],[f63,f57])).
% 1.49/0.55  fof(f57,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f7])).
% 1.49/0.55  fof(f7,axiom,(
% 1.49/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.49/0.55  fof(f63,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f36])).
% 1.49/0.55  fof(f36,plain,(
% 1.49/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f3])).
% 1.49/0.55  fof(f3,axiom,(
% 1.49/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.49/0.55  fof(f149,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.49/0.55    inference(forward_demodulation,[],[f135,f79])).
% 1.49/0.55  fof(f79,plain,(
% 1.49/0.55    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.49/0.55    inference(superposition,[],[f54,f44])).
% 1.49/0.55  fof(f135,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.49/0.55    inference(superposition,[],[f64,f43])).
% 1.49/0.55  fof(f150,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k2_xboole_0(X1,X0)))) )),
% 1.49/0.55    inference(backward_demodulation,[],[f70,f149])).
% 1.49/0.55  fof(f70,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k2_xboole_0(X1,X0)))))) )),
% 1.49/0.55    inference(backward_demodulation,[],[f66,f64])).
% 1.49/0.55  fof(f66,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))))) )),
% 1.49/0.55    inference(definition_unfolding,[],[f55,f65])).
% 1.49/0.55  fof(f65,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 1.49/0.55    inference(definition_unfolding,[],[f56,f57])).
% 1.49/0.55  fof(f56,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f2])).
% 1.49/0.55  fof(f2,axiom,(
% 1.49/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.49/0.55  fof(f55,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f8])).
% 1.49/0.55  fof(f8,axiom,(
% 1.49/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.49/0.55  fof(f2199,plain,(
% 1.49/0.55    ( ! [X7] : (r1_tarski(k5_xboole_0(k1_relat_1(sK1),k5_xboole_0(X7,k2_xboole_0(k1_relat_1(sK1),X7))),k10_relat_1(sK1,k9_relat_1(sK1,X7)))) )),
% 1.49/0.55    inference(backward_demodulation,[],[f381,f2198])).
% 1.49/0.55  fof(f2198,plain,(
% 1.49/0.55    ( ! [X7] : (k10_relat_1(sK1,X7) = k9_relat_1(k4_relat_1(sK1),X7)) )),
% 1.49/0.55    inference(forward_demodulation,[],[f2195,f2185])).
% 1.49/0.55  fof(f2185,plain,(
% 1.49/0.55    ( ! [X7] : (k10_relat_1(sK1,X7) = k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7))) )),
% 1.49/0.55    inference(backward_demodulation,[],[f964,f2184])).
% 1.49/0.55  fof(f2184,plain,(
% 1.49/0.55    ( ! [X1] : (k4_relat_1(k8_relat_1(X1,sK1)) = k7_relat_1(k4_relat_1(sK1),X1)) )),
% 1.49/0.55    inference(backward_demodulation,[],[f377,f2181])).
% 1.49/0.55  fof(f2181,plain,(
% 1.49/0.55    ( ! [X7] : (k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))) )),
% 1.49/0.55    inference(resolution,[],[f109,f39])).
% 1.49/0.55  fof(f39,plain,(
% 1.49/0.55    v1_relat_1(sK1)),
% 1.49/0.55    inference(cnf_transformation,[],[f38])).
% 1.49/0.55  fof(f109,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) )),
% 1.49/0.55    inference(resolution,[],[f60,f48])).
% 1.49/0.55  fof(f48,plain,(
% 1.49/0.55    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f26])).
% 1.49/0.55  fof(f26,plain,(
% 1.49/0.55    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f9])).
% 1.49/0.55  fof(f9,axiom,(
% 1.49/0.55    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.49/0.55  fof(f60,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f33])).
% 1.49/0.55  fof(f33,plain,(
% 1.49/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f21])).
% 1.49/0.55  fof(f21,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.49/0.55  fof(f377,plain,(
% 1.49/0.55    ( ! [X1] : (k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X1,sK1))) )),
% 1.49/0.55    inference(forward_demodulation,[],[f376,f102])).
% 1.49/0.55  fof(f102,plain,(
% 1.49/0.55    ( ! [X7] : (k8_relat_1(X7,sK1) = k5_relat_1(sK1,k6_relat_1(X7))) )),
% 1.49/0.55    inference(resolution,[],[f59,f39])).
% 1.49/0.55  fof(f59,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f32])).
% 1.49/0.55  fof(f32,plain,(
% 1.49/0.55    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f13])).
% 1.49/0.55  fof(f13,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.49/0.55  fof(f376,plain,(
% 1.49/0.55    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1))) )),
% 1.49/0.55    inference(forward_demodulation,[],[f373,f45])).
% 1.49/0.55  fof(f45,plain,(
% 1.49/0.55    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f20])).
% 1.49/0.55  fof(f20,axiom,(
% 1.49/0.55    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 1.49/0.55  fof(f373,plain,(
% 1.49/0.55    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(sK1))) )),
% 1.49/0.55    inference(resolution,[],[f362,f42])).
% 1.49/0.55  fof(f42,plain,(
% 1.49/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f10])).
% 1.49/0.55  fof(f10,axiom,(
% 1.49/0.55    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.49/0.55  fof(f362,plain,(
% 1.49/0.55    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1))) )),
% 1.49/0.55    inference(resolution,[],[f53,f39])).
% 1.49/0.55  fof(f53,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f30])).
% 1.49/0.55  fof(f30,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f18])).
% 1.49/0.55  fof(f18,axiom,(
% 1.49/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.49/0.55  fof(f964,plain,(
% 1.49/0.55    ( ! [X7] : (k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1))) = k10_relat_1(sK1,X7)) )),
% 1.49/0.55    inference(forward_demodulation,[],[f963,f371])).
% 1.49/0.55  fof(f371,plain,(
% 1.49/0.55    ( ! [X1] : (k10_relat_1(sK1,X1) = k1_relat_1(k8_relat_1(X1,sK1))) )),
% 1.49/0.55    inference(forward_demodulation,[],[f370,f102])).
% 1.49/0.55  fof(f370,plain,(
% 1.49/0.55    ( ! [X1] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k10_relat_1(sK1,X1)) )),
% 1.49/0.55    inference(forward_demodulation,[],[f367,f46])).
% 1.49/0.55  fof(f46,plain,(
% 1.49/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f19])).
% 1.49/0.55  fof(f19,axiom,(
% 1.49/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.49/0.55  fof(f367,plain,(
% 1.49/0.55    ( ! [X1] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X1)))) )),
% 1.49/0.55    inference(resolution,[],[f299,f42])).
% 1.49/0.55  fof(f299,plain,(
% 1.49/0.55    ( ! [X7] : (~v1_relat_1(X7) | k1_relat_1(k5_relat_1(sK1,X7)) = k10_relat_1(sK1,k1_relat_1(X7))) )),
% 1.49/0.55    inference(resolution,[],[f52,f39])).
% 1.49/0.55  fof(f52,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f29])).
% 1.49/0.55  fof(f29,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f16])).
% 1.49/0.55  fof(f16,axiom,(
% 1.49/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.49/0.55  fof(f963,plain,(
% 1.49/0.55    ( ! [X7] : (k1_relat_1(k8_relat_1(X7,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1)))) )),
% 1.49/0.55    inference(resolution,[],[f95,f39])).
% 1.49/0.55  fof(f95,plain,(
% 1.49/0.55    ( ! [X2,X3] : (~v1_relat_1(X3) | k1_relat_1(k8_relat_1(X2,X3)) = k2_relat_1(k4_relat_1(k8_relat_1(X2,X3)))) )),
% 1.49/0.55    inference(resolution,[],[f51,f58])).
% 1.49/0.55  fof(f58,plain,(
% 1.49/0.55    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f31])).
% 1.49/0.55  fof(f31,plain,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f11])).
% 1.49/0.55  fof(f11,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 1.49/0.55  fof(f51,plain,(
% 1.49/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f28])).
% 1.49/0.55  fof(f28,plain,(
% 1.49/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f17])).
% 1.49/0.55  fof(f17,axiom,(
% 1.49/0.55    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.49/0.55  fof(f2195,plain,(
% 1.49/0.55    ( ! [X7] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)) )),
% 1.49/0.55    inference(resolution,[],[f114,f39])).
% 1.49/0.55  fof(f114,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)) )),
% 1.49/0.55    inference(resolution,[],[f61,f48])).
% 1.49/0.55  fof(f61,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f34])).
% 1.49/0.55  fof(f34,plain,(
% 1.49/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f14])).
% 1.49/0.55  fof(f14,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.49/0.55  fof(f381,plain,(
% 1.49/0.55    ( ! [X7] : (r1_tarski(k5_xboole_0(k1_relat_1(sK1),k5_xboole_0(X7,k2_xboole_0(k1_relat_1(sK1),X7))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X7)))) )),
% 1.49/0.55    inference(resolution,[],[f71,f39])).
% 1.49/0.55  fof(f71,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_xboole_0(k1_relat_1(X1),k5_xboole_0(X0,k2_xboole_0(k1_relat_1(X1),X0))),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))) )),
% 1.49/0.55    inference(backward_demodulation,[],[f67,f64])).
% 1.49/0.55  fof(f67,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(X1),X0),k2_xboole_0(k1_relat_1(X1),X0)),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 1.49/0.55    inference(definition_unfolding,[],[f62,f57])).
% 1.49/0.55  fof(f62,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f35])).
% 1.49/0.55  fof(f35,plain,(
% 1.49/0.55    ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f15])).
% 1.49/0.55  fof(f15,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 1.49/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).
% 1.49/0.55  % SZS output end Proof for theBenchmark
% 1.49/0.55  % (29742)------------------------------
% 1.49/0.55  % (29742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (29742)Termination reason: Refutation
% 1.49/0.55  
% 1.49/0.55  % (29742)Memory used [KB]: 5628
% 1.49/0.55  % (29742)Time elapsed: 0.129 s
% 1.49/0.55  % (29742)------------------------------
% 1.49/0.55  % (29742)------------------------------
% 1.49/0.55  % (29740)Success in time 0.189 s
%------------------------------------------------------------------------------
