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
% DateTime   : Thu Dec  3 12:52:17 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 501 expanded)
%              Number of leaves         :   17 ( 137 expanded)
%              Depth                    :   19
%              Number of atoms          :  139 ( 831 expanded)
%              Number of equality atoms :   83 ( 385 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3520,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3519,f776])).

fof(f776,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) ),
    inference(forward_demodulation,[],[f762,f42])).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f762,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(superposition,[],[f77,f508])).

fof(f508,plain,(
    ! [X3] : k6_relat_1(k1_relat_1(k7_relat_1(sK1,X3))) = k7_relat_1(k6_relat_1(k1_relat_1(sK1)),X3) ),
    inference(forward_demodulation,[],[f480,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f480,plain,(
    ! [X3] : k7_relat_1(k6_relat_1(k1_relat_1(sK1)),X3) = k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK1,X3))))) ),
    inference(superposition,[],[f450,f259])).

fof(f259,plain,(
    ! [X0] : k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f258,f115])).

fof(f115,plain,(
    ! [X0] : k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f88,f38])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f36])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
        & v1_relat_1(X1) )
   => ( k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(k7_relat_1(X0,X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f87,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f86,f80])).

fof(f80,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f54,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f56,f42])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f258,plain,(
    ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f256,f41])).

fof(f256,plain,(
    ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))))) ),
    inference(resolution,[],[f251,f40])).

fof(f251,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(sK1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(X0)))) ) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f450,plain,(
    ! [X2,X1] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(backward_demodulation,[],[f116,f449])).

fof(f449,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ),
    inference(forward_demodulation,[],[f441,f41])).

fof(f441,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(k6_relat_1(X1))))) ),
    inference(resolution,[],[f254,f40])).

fof(f254,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X2) = k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(X1)))) ) ),
    inference(forward_demodulation,[],[f252,f41])).

fof(f252,plain,(
    ! [X2,X1] :
      ( k7_relat_1(X1,k1_relat_1(k6_relat_1(X2))) = k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f44,f40])).

fof(f116,plain,(
    ! [X2,X1] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(resolution,[],[f88,f40])).

fof(f77,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(resolution,[],[f53,f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f3519,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) ),
    inference(superposition,[],[f82,f3304])).

fof(f3304,plain,(
    ! [X2,X3] : k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)) = k9_relat_1(k6_relat_1(X3),X2) ),
    inference(forward_demodulation,[],[f3213,f509])).

fof(f509,plain,(
    ! [X4,X5] : k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k6_relat_1(X5),X4) ),
    inference(forward_demodulation,[],[f484,f77])).

fof(f484,plain,(
    ! [X4,X5] : k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) = k2_relat_1(k7_relat_1(k6_relat_1(X5),X4)) ),
    inference(superposition,[],[f42,f450])).

fof(f3213,plain,(
    ! [X2,X3] : k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f41,f1038])).

fof(f1038,plain,(
    ! [X6,X7] : k6_relat_1(k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,X7))) = k7_relat_1(k6_relat_1(X6),X7) ),
    inference(backward_demodulation,[],[f91,f1037])).

fof(f1037,plain,(
    ! [X6,X7] : k7_relat_1(k6_relat_1(X6),k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,X7))) = k7_relat_1(k6_relat_1(X6),X7) ),
    inference(forward_demodulation,[],[f1031,f522])).

fof(f522,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X2),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X2),X1)) ),
    inference(backward_demodulation,[],[f450,f509])).

fof(f1031,plain,(
    ! [X6,X7] : k7_relat_1(k6_relat_1(X6),k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,X7))) = k6_relat_1(k9_relat_1(k6_relat_1(X6),X7)) ),
    inference(superposition,[],[f522,f293])).

fof(f293,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k6_relat_1(X1),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(forward_demodulation,[],[f291,f41])).

fof(f291,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k6_relat_1(X1),k1_setfam_1(k4_enumset1(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),X2))) ),
    inference(resolution,[],[f67,f40])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f91,plain,(
    ! [X6,X7] : k6_relat_1(k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,X7))) = k7_relat_1(k6_relat_1(X6),k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,X7))) ),
    inference(resolution,[],[f87,f65])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f82,plain,(
    k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK1))) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f68,f79])).

fof(f79,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(resolution,[],[f54,f38])).

fof(f68,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f64,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f47,f62,f62])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f64,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k4_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) ),
    inference(definition_unfolding,[],[f39,f63])).

fof(f39,plain,(
    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:59:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (19002)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (19010)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (19004)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (18998)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (19008)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (19006)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (19012)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (19011)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (18997)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (18993)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (19005)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (19001)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (18999)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.53  % (18994)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.53  % (19000)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (19009)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.54  % (18995)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.55  % (19007)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 2.17/0.64  % (19004)Refutation found. Thanks to Tanya!
% 2.17/0.64  % SZS status Theorem for theBenchmark
% 2.17/0.64  % SZS output start Proof for theBenchmark
% 2.17/0.64  fof(f3520,plain,(
% 2.17/0.64    $false),
% 2.17/0.64    inference(subsumption_resolution,[],[f3519,f776])).
% 2.17/0.64  fof(f776,plain,(
% 2.17/0.64    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) )),
% 2.17/0.64    inference(forward_demodulation,[],[f762,f42])).
% 2.17/0.64  fof(f42,plain,(
% 2.17/0.64    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.17/0.64    inference(cnf_transformation,[],[f14])).
% 2.17/0.64  fof(f14,axiom,(
% 2.17/0.64    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.17/0.64  fof(f762,plain,(
% 2.17/0.64    ( ! [X0] : (k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))))) )),
% 2.17/0.64    inference(superposition,[],[f77,f508])).
% 2.17/0.64  fof(f508,plain,(
% 2.17/0.64    ( ! [X3] : (k6_relat_1(k1_relat_1(k7_relat_1(sK1,X3))) = k7_relat_1(k6_relat_1(k1_relat_1(sK1)),X3)) )),
% 2.17/0.64    inference(forward_demodulation,[],[f480,f41])).
% 2.17/0.64  fof(f41,plain,(
% 2.17/0.64    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.17/0.64    inference(cnf_transformation,[],[f14])).
% 2.17/0.64  fof(f480,plain,(
% 2.17/0.64    ( ! [X3] : (k7_relat_1(k6_relat_1(k1_relat_1(sK1)),X3) = k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK1,X3)))))) )),
% 2.17/0.64    inference(superposition,[],[f450,f259])).
% 2.17/0.64  fof(f259,plain,(
% 2.17/0.64    ( ! [X0] : (k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) )),
% 2.17/0.64    inference(forward_demodulation,[],[f258,f115])).
% 2.17/0.64  fof(f115,plain,(
% 2.17/0.64    ( ! [X0] : (k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.17/0.64    inference(resolution,[],[f88,f38])).
% 2.17/0.64  fof(f38,plain,(
% 2.17/0.64    v1_relat_1(sK1)),
% 2.17/0.64    inference(cnf_transformation,[],[f37])).
% 2.17/0.64  fof(f37,plain,(
% 2.17/0.64    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) & v1_relat_1(sK1)),
% 2.17/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f36])).
% 2.17/0.64  fof(f36,plain,(
% 2.17/0.64    ? [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) & v1_relat_1(X1)) => (k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) & v1_relat_1(sK1))),
% 2.17/0.64    introduced(choice_axiom,[])).
% 2.17/0.64  fof(f24,plain,(
% 2.17/0.64    ? [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) & v1_relat_1(X1))),
% 2.17/0.64    inference(ennf_transformation,[],[f22])).
% 2.17/0.64  fof(f22,plain,(
% 2.17/0.64    ~! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 2.17/0.64    inference(pure_predicate_removal,[],[f21])).
% 2.17/0.64  fof(f21,negated_conjecture,(
% 2.17/0.64    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 2.17/0.64    inference(negated_conjecture,[],[f20])).
% 2.17/0.64  fof(f20,conjecture,(
% 2.17/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).
% 2.17/0.64  fof(f88,plain,(
% 2.17/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | k6_relat_1(k1_relat_1(k7_relat_1(X0,X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(X0,X1)))) )),
% 2.17/0.64    inference(resolution,[],[f87,f51])).
% 2.17/0.64  fof(f51,plain,(
% 2.17/0.64    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.17/0.64    inference(cnf_transformation,[],[f29])).
% 2.17/0.64  fof(f29,plain,(
% 2.17/0.64    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.17/0.64    inference(ennf_transformation,[],[f16])).
% 2.17/0.64  fof(f16,axiom,(
% 2.17/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 2.17/0.64  fof(f87,plain,(
% 2.17/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 2.17/0.64    inference(forward_demodulation,[],[f86,f80])).
% 2.17/0.64  fof(f80,plain,(
% 2.17/0.64    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 2.17/0.64    inference(resolution,[],[f54,f40])).
% 2.17/0.64  fof(f40,plain,(
% 2.17/0.64    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.17/0.64    inference(cnf_transformation,[],[f23])).
% 2.17/0.64  fof(f23,plain,(
% 2.17/0.64    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.17/0.64    inference(pure_predicate_removal,[],[f19])).
% 2.17/0.64  fof(f19,axiom,(
% 2.17/0.64    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.17/0.64  fof(f54,plain,(
% 2.17/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.17/0.64    inference(cnf_transformation,[],[f32])).
% 2.17/0.64  fof(f32,plain,(
% 2.17/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.17/0.64    inference(ennf_transformation,[],[f18])).
% 2.17/0.64  fof(f18,axiom,(
% 2.17/0.64    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.17/0.64  fof(f86,plain,(
% 2.17/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 2.17/0.64    inference(subsumption_resolution,[],[f83,f40])).
% 2.17/0.64  fof(f83,plain,(
% 2.17/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.17/0.64    inference(superposition,[],[f56,f42])).
% 2.17/0.64  fof(f56,plain,(
% 2.17/0.64    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 2.17/0.64    inference(cnf_transformation,[],[f35])).
% 2.17/0.64  fof(f35,plain,(
% 2.17/0.64    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.17/0.64    inference(flattening,[],[f34])).
% 2.17/0.64  fof(f34,plain,(
% 2.17/0.64    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.17/0.64    inference(ennf_transformation,[],[f15])).
% 2.17/0.64  fof(f15,axiom,(
% 2.17/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 2.17/0.64  fof(f258,plain,(
% 2.17/0.64    ( ! [X0] : (k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) )),
% 2.17/0.64    inference(forward_demodulation,[],[f256,f41])).
% 2.17/0.64  fof(f256,plain,(
% 2.17/0.64    ( ! [X0] : (k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0)))))) )),
% 2.17/0.64    inference(resolution,[],[f251,f40])).
% 2.17/0.64  fof(f251,plain,(
% 2.17/0.64    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(sK1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(X0))))) )),
% 2.17/0.64    inference(resolution,[],[f44,f38])).
% 2.17/0.64  fof(f44,plain,(
% 2.17/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 2.17/0.64    inference(cnf_transformation,[],[f26])).
% 2.17/0.64  fof(f26,plain,(
% 2.17/0.64    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.17/0.64    inference(ennf_transformation,[],[f13])).
% 2.17/0.64  fof(f13,axiom,(
% 2.17/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).
% 2.17/0.64  fof(f450,plain,(
% 2.17/0.64    ( ! [X2,X1] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X2),X1)) )),
% 2.17/0.64    inference(backward_demodulation,[],[f116,f449])).
% 2.17/0.64  fof(f449,plain,(
% 2.17/0.64    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)))) )),
% 2.17/0.64    inference(forward_demodulation,[],[f441,f41])).
% 2.17/0.64  fof(f441,plain,(
% 2.17/0.64    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(k6_relat_1(X1)))))) )),
% 2.17/0.64    inference(resolution,[],[f254,f40])).
% 2.17/0.64  fof(f254,plain,(
% 2.17/0.64    ( ! [X2,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X2) = k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(X1))))) )),
% 2.17/0.64    inference(forward_demodulation,[],[f252,f41])).
% 2.17/0.64  fof(f252,plain,(
% 2.17/0.64    ( ! [X2,X1] : (k7_relat_1(X1,k1_relat_1(k6_relat_1(X2))) = k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 2.17/0.64    inference(resolution,[],[f44,f40])).
% 2.17/0.64  fof(f116,plain,(
% 2.17/0.64    ( ! [X2,X1] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))) )),
% 2.17/0.64    inference(resolution,[],[f88,f40])).
% 2.17/0.64  fof(f77,plain,(
% 2.17/0.64    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))) )),
% 2.17/0.64    inference(resolution,[],[f53,f40])).
% 2.17/0.64  fof(f53,plain,(
% 2.17/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 2.17/0.64    inference(cnf_transformation,[],[f31])).
% 2.17/0.64  fof(f31,plain,(
% 2.17/0.64    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.17/0.64    inference(ennf_transformation,[],[f11])).
% 2.17/0.64  fof(f11,axiom,(
% 2.17/0.64    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.17/0.64  fof(f3519,plain,(
% 2.17/0.64    k1_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0)),
% 2.17/0.64    inference(superposition,[],[f82,f3304])).
% 2.17/0.64  fof(f3304,plain,(
% 2.17/0.64    ( ! [X2,X3] : (k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)) = k9_relat_1(k6_relat_1(X3),X2)) )),
% 2.17/0.64    inference(forward_demodulation,[],[f3213,f509])).
% 2.17/0.64  fof(f509,plain,(
% 2.17/0.64    ( ! [X4,X5] : (k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k6_relat_1(X5),X4)) )),
% 2.17/0.64    inference(forward_demodulation,[],[f484,f77])).
% 2.17/0.64  fof(f484,plain,(
% 2.17/0.64    ( ! [X4,X5] : (k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) = k2_relat_1(k7_relat_1(k6_relat_1(X5),X4))) )),
% 2.17/0.64    inference(superposition,[],[f42,f450])).
% 2.17/0.64  fof(f3213,plain,(
% 2.17/0.64    ( ! [X2,X3] : (k1_setfam_1(k4_enumset1(X2,X2,X2,X2,X2,X3)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) )),
% 2.17/0.64    inference(superposition,[],[f41,f1038])).
% 2.17/0.64  fof(f1038,plain,(
% 2.17/0.64    ( ! [X6,X7] : (k6_relat_1(k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,X7))) = k7_relat_1(k6_relat_1(X6),X7)) )),
% 2.17/0.64    inference(backward_demodulation,[],[f91,f1037])).
% 2.17/0.64  fof(f1037,plain,(
% 2.17/0.64    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,X7))) = k7_relat_1(k6_relat_1(X6),X7)) )),
% 2.17/0.64    inference(forward_demodulation,[],[f1031,f522])).
% 2.17/0.64  fof(f522,plain,(
% 2.17/0.64    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X2),X1) = k6_relat_1(k9_relat_1(k6_relat_1(X2),X1))) )),
% 2.17/0.64    inference(backward_demodulation,[],[f450,f509])).
% 2.17/0.64  fof(f1031,plain,(
% 2.17/0.64    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,X7))) = k6_relat_1(k9_relat_1(k6_relat_1(X6),X7))) )),
% 2.17/0.64    inference(superposition,[],[f522,f293])).
% 2.17/0.64  fof(f293,plain,(
% 2.17/0.64    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k6_relat_1(X1),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)))) )),
% 2.17/0.64    inference(forward_demodulation,[],[f291,f41])).
% 2.17/0.64  fof(f291,plain,(
% 2.17/0.64    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),X2) = k9_relat_1(k6_relat_1(X1),k1_setfam_1(k4_enumset1(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)),X2)))) )),
% 2.17/0.64    inference(resolution,[],[f67,f40])).
% 2.17/0.64  fof(f67,plain,(
% 2.17/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 2.17/0.64    inference(definition_unfolding,[],[f55,f63])).
% 2.17/0.64  fof(f63,plain,(
% 2.17/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 2.17/0.64    inference(definition_unfolding,[],[f48,f62])).
% 2.17/0.64  fof(f62,plain,(
% 2.17/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 2.17/0.64    inference(definition_unfolding,[],[f49,f61])).
% 2.17/0.64  fof(f61,plain,(
% 2.17/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 2.17/0.64    inference(definition_unfolding,[],[f57,f60])).
% 2.17/0.64  fof(f60,plain,(
% 2.17/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 2.17/0.64    inference(definition_unfolding,[],[f58,f59])).
% 2.17/0.64  fof(f59,plain,(
% 2.17/0.64    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.17/0.64    inference(cnf_transformation,[],[f6])).
% 2.17/0.64  fof(f6,axiom,(
% 2.17/0.64    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.17/0.64  fof(f58,plain,(
% 2.17/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.17/0.64    inference(cnf_transformation,[],[f5])).
% 2.17/0.64  fof(f5,axiom,(
% 2.17/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.17/0.64  fof(f57,plain,(
% 2.17/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.17/0.64    inference(cnf_transformation,[],[f4])).
% 2.17/0.64  fof(f4,axiom,(
% 2.17/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.17/0.64  fof(f49,plain,(
% 2.17/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.17/0.64    inference(cnf_transformation,[],[f3])).
% 2.17/0.64  fof(f3,axiom,(
% 2.17/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.17/0.64  fof(f48,plain,(
% 2.17/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.17/0.64    inference(cnf_transformation,[],[f7])).
% 2.17/0.64  fof(f7,axiom,(
% 2.17/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.17/0.64  fof(f55,plain,(
% 2.17/0.64    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.17/0.64    inference(cnf_transformation,[],[f33])).
% 2.17/0.64  fof(f33,plain,(
% 2.17/0.64    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.17/0.64    inference(ennf_transformation,[],[f9])).
% 2.17/0.64  fof(f9,axiom,(
% 2.17/0.64    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 2.17/0.64  fof(f91,plain,(
% 2.17/0.64    ( ! [X6,X7] : (k6_relat_1(k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,X7))) = k7_relat_1(k6_relat_1(X6),k1_setfam_1(k4_enumset1(X6,X6,X6,X6,X6,X7)))) )),
% 2.17/0.64    inference(resolution,[],[f87,f65])).
% 2.17/0.64  fof(f65,plain,(
% 2.17/0.64    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 2.17/0.64    inference(definition_unfolding,[],[f46,f63])).
% 2.17/0.64  fof(f46,plain,(
% 2.17/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.17/0.64    inference(cnf_transformation,[],[f1])).
% 2.17/0.64  fof(f1,axiom,(
% 2.17/0.64    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.17/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.17/0.65  fof(f82,plain,(
% 2.17/0.65    k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK1))) != k1_relat_1(k7_relat_1(sK1,sK0))),
% 2.17/0.65    inference(backward_demodulation,[],[f68,f79])).
% 2.17/0.65  fof(f79,plain,(
% 2.17/0.65    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 2.17/0.65    inference(resolution,[],[f54,f38])).
% 2.17/0.65  fof(f68,plain,(
% 2.17/0.65    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k1_relat_1(sK1)))),
% 2.17/0.65    inference(backward_demodulation,[],[f64,f66])).
% 2.17/0.65  fof(f66,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 2.17/0.65    inference(definition_unfolding,[],[f47,f62,f62])).
% 2.17/0.65  fof(f47,plain,(
% 2.17/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f2])).
% 2.17/0.65  fof(f2,axiom,(
% 2.17/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.17/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.17/0.65  fof(f64,plain,(
% 2.17/0.65    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) != k1_setfam_1(k4_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))),
% 2.17/0.65    inference(definition_unfolding,[],[f39,f63])).
% 2.17/0.65  fof(f39,plain,(
% 2.17/0.65    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 2.17/0.65    inference(cnf_transformation,[],[f37])).
% 2.17/0.65  % SZS output end Proof for theBenchmark
% 2.17/0.65  % (19004)------------------------------
% 2.17/0.65  % (19004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.65  % (19004)Termination reason: Refutation
% 2.17/0.65  
% 2.17/0.65  % (19004)Memory used [KB]: 12792
% 2.17/0.65  % (19004)Time elapsed: 0.237 s
% 2.17/0.65  % (19004)------------------------------
% 2.17/0.65  % (19004)------------------------------
% 2.17/0.65  % (18986)Success in time 0.285 s
%------------------------------------------------------------------------------
