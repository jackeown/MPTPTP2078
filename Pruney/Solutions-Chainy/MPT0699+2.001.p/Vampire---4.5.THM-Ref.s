%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:09 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 295 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  201 ( 993 expanded)
%              Number of equality atoms :   78 ( 279 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f912,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f911])).

fof(f911,plain,(
    k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0) ),
    inference(superposition,[],[f118,f888])).

fof(f888,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,X0) ),
    inference(backward_demodulation,[],[f514,f775])).

fof(f775,plain,(
    ! [X19] : k9_relat_1(sK1,X19) = k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X19)) ),
    inference(backward_demodulation,[],[f621,f774])).

fof(f774,plain,(
    ! [X6,X7] : k1_setfam_1(k1_enumset1(X6,X6,X7)) = k10_relat_1(k6_relat_1(X6),X7) ),
    inference(forward_demodulation,[],[f689,f338])).

fof(f338,plain,(
    ! [X12,X13] : k1_relat_1(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13))) = k10_relat_1(k6_relat_1(X12),X13) ),
    inference(resolution,[],[f233,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f233,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | k1_relat_1(k5_relat_1(X12,k6_relat_1(X13))) = k10_relat_1(X12,X13) ) ),
    inference(forward_demodulation,[],[f225,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f225,plain,(
    ! [X12,X13] :
      ( k1_relat_1(k5_relat_1(X12,k6_relat_1(X13))) = k10_relat_1(X12,k1_relat_1(k6_relat_1(X13)))
      | ~ v1_relat_1(X12) ) ),
    inference(resolution,[],[f45,f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f689,plain,(
    ! [X6,X7] : k1_setfam_1(k1_enumset1(X6,X6,X7)) = k1_relat_1(k5_relat_1(k6_relat_1(X6),k6_relat_1(X7))) ),
    inference(superposition,[],[f41,f181])).

fof(f181,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f61,f60])).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f51,f52,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f61,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f52])).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f621,plain,(
    ! [X19] : k9_relat_1(sK1,X19) = k9_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X19))) ),
    inference(resolution,[],[f62,f35])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f514,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0)) ),
    inference(forward_demodulation,[],[f513,f446])).

fof(f446,plain,(
    ! [X19] : k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X19)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X19) ),
    inference(forward_demodulation,[],[f445,f290])).

fof(f290,plain,(
    k5_relat_1(sK1,k4_relat_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f289,f116])).

fof(f116,plain,(
    k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f115,f35])).

fof(f115,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f113,f36])).

fof(f36,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f113,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f289,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f288,f35])).

fof(f288,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f283,f36])).

fof(f283,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f49,f37])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f445,plain,(
    ! [X19] : k10_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)),X19) = k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X19)) ),
    inference(resolution,[],[f400,f35])).

fof(f400,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | k10_relat_1(k5_relat_1(X14,k4_relat_1(sK1)),X15) = k10_relat_1(X14,k10_relat_1(k4_relat_1(sK1),X15)) ) ),
    inference(resolution,[],[f57,f119])).

fof(f119,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f64,f116])).

fof(f64,plain,(
    v1_relat_1(k2_funct_1(sK1)) ),
    inference(subsumption_resolution,[],[f63,f35])).

fof(f63,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f46,f36])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f513,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X0))) ),
    inference(subsumption_resolution,[],[f512,f35])).

fof(f512,plain,(
    ! [X0] :
      ( k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X0)))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f498,f36])).

fof(f498,plain,(
    ! [X0] :
      ( k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X0)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f58,f144])).

fof(f144,plain,(
    ! [X3] : r1_tarski(k10_relat_1(k4_relat_1(sK1),X3),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f135,f81])).

fof(f81,plain,(
    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f43,f35])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f135,plain,(
    ! [X3] : r1_tarski(k10_relat_1(k4_relat_1(sK1),X3),k1_relat_1(k4_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f97,f116])).

fof(f97,plain,(
    ! [X3] : r1_tarski(k10_relat_1(k2_funct_1(sK1),X3),k1_relat_1(k2_funct_1(sK1))) ),
    inference(resolution,[],[f55,f64])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f118,plain,(
    k9_relat_1(sK1,sK0) != k10_relat_1(k4_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f38,f116])).

fof(f38,plain,(
    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (12389)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (12403)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (12398)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (12404)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (12401)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (12396)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (12395)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (12393)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (12402)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (12397)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (12392)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (12391)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (12406)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (12390)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (12399)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (12407)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.24/0.51  % (12400)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.24/0.52  % (12405)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.36/0.53  % (12402)Refutation found. Thanks to Tanya!
% 1.36/0.53  % SZS status Theorem for theBenchmark
% 1.36/0.53  % SZS output start Proof for theBenchmark
% 1.36/0.53  fof(f912,plain,(
% 1.36/0.53    $false),
% 1.36/0.53    inference(trivial_inequality_removal,[],[f911])).
% 1.36/0.53  fof(f911,plain,(
% 1.36/0.53    k9_relat_1(sK1,sK0) != k9_relat_1(sK1,sK0)),
% 1.36/0.53    inference(superposition,[],[f118,f888])).
% 1.36/0.53  fof(f888,plain,(
% 1.36/0.53    ( ! [X0] : (k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,X0)) )),
% 1.36/0.53    inference(backward_demodulation,[],[f514,f775])).
% 1.36/0.53  fof(f775,plain,(
% 1.36/0.53    ( ! [X19] : (k9_relat_1(sK1,X19) = k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X19))) )),
% 1.36/0.53    inference(backward_demodulation,[],[f621,f774])).
% 1.36/0.53  fof(f774,plain,(
% 1.36/0.53    ( ! [X6,X7] : (k1_setfam_1(k1_enumset1(X6,X6,X7)) = k10_relat_1(k6_relat_1(X6),X7)) )),
% 1.36/0.53    inference(forward_demodulation,[],[f689,f338])).
% 1.36/0.53  fof(f338,plain,(
% 1.36/0.53    ( ! [X12,X13] : (k1_relat_1(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13))) = k10_relat_1(k6_relat_1(X12),X13)) )),
% 1.36/0.53    inference(resolution,[],[f233,f39])).
% 1.36/0.53  fof(f39,plain,(
% 1.36/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f12])).
% 1.36/0.53  fof(f12,axiom,(
% 1.36/0.53    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.36/0.53  fof(f233,plain,(
% 1.36/0.53    ( ! [X12,X13] : (~v1_relat_1(X12) | k1_relat_1(k5_relat_1(X12,k6_relat_1(X13))) = k10_relat_1(X12,X13)) )),
% 1.36/0.53    inference(forward_demodulation,[],[f225,f41])).
% 1.36/0.53  fof(f41,plain,(
% 1.36/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.36/0.53    inference(cnf_transformation,[],[f9])).
% 1.36/0.53  fof(f9,axiom,(
% 1.36/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.36/0.53  fof(f225,plain,(
% 1.36/0.53    ( ! [X12,X13] : (k1_relat_1(k5_relat_1(X12,k6_relat_1(X13))) = k10_relat_1(X12,k1_relat_1(k6_relat_1(X13))) | ~v1_relat_1(X12)) )),
% 1.36/0.53    inference(resolution,[],[f45,f39])).
% 1.36/0.53  fof(f45,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f21])).
% 1.36/0.53  fof(f21,plain,(
% 1.36/0.53    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f7])).
% 1.36/0.53  fof(f7,axiom,(
% 1.36/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.36/0.53  fof(f689,plain,(
% 1.36/0.53    ( ! [X6,X7] : (k1_setfam_1(k1_enumset1(X6,X6,X7)) = k1_relat_1(k5_relat_1(k6_relat_1(X6),k6_relat_1(X7)))) )),
% 1.36/0.53    inference(superposition,[],[f41,f181])).
% 1.36/0.53  fof(f181,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X0)))) )),
% 1.36/0.53    inference(superposition,[],[f61,f60])).
% 1.36/0.53  fof(f60,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.36/0.53    inference(definition_unfolding,[],[f51,f52,f52])).
% 1.36/0.53  fof(f52,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f2])).
% 1.36/0.53  fof(f2,axiom,(
% 1.36/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.53  fof(f51,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f1])).
% 1.36/0.53  fof(f1,axiom,(
% 1.36/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.36/0.53  fof(f61,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.36/0.53    inference(definition_unfolding,[],[f54,f59])).
% 1.36/0.53  fof(f59,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.36/0.53    inference(definition_unfolding,[],[f53,f52])).
% 1.36/0.53  fof(f53,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f3])).
% 1.36/0.53  fof(f3,axiom,(
% 1.36/0.53    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.36/0.53  fof(f54,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f14])).
% 1.36/0.53  fof(f14,axiom,(
% 1.36/0.53    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.36/0.53  fof(f621,plain,(
% 1.36/0.53    ( ! [X19] : (k9_relat_1(sK1,X19) = k9_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X19)))) )),
% 1.36/0.53    inference(resolution,[],[f62,f35])).
% 1.36/0.53  fof(f35,plain,(
% 1.36/0.53    v1_relat_1(sK1)),
% 1.36/0.53    inference(cnf_transformation,[],[f34])).
% 1.36/0.53  fof(f34,plain,(
% 1.36/0.53    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.36/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f33])).
% 1.36/0.53  fof(f33,plain,(
% 1.36/0.53    ? [X0,X1] : (k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.36/0.53    introduced(choice_axiom,[])).
% 1.36/0.53  fof(f19,plain,(
% 1.36/0.53    ? [X0,X1] : (k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.36/0.53    inference(flattening,[],[f18])).
% 1.36/0.53  fof(f18,plain,(
% 1.36/0.53    ? [X0,X1] : ((k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.36/0.53    inference(ennf_transformation,[],[f17])).
% 1.36/0.53  fof(f17,negated_conjecture,(
% 1.36/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.36/0.53    inference(negated_conjecture,[],[f16])).
% 1.36/0.53  fof(f16,conjecture,(
% 1.36/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 1.36/0.53  fof(f62,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)))) )),
% 1.36/0.53    inference(definition_unfolding,[],[f56,f59])).
% 1.36/0.53  fof(f56,plain,(
% 1.36/0.53    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f29])).
% 1.36/0.53  fof(f29,plain,(
% 1.36/0.53    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f4])).
% 1.36/0.53  fof(f4,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).
% 1.36/0.53  fof(f514,plain,(
% 1.36/0.53    ( ! [X0] : (k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X0))) )),
% 1.36/0.53    inference(forward_demodulation,[],[f513,f446])).
% 1.36/0.53  fof(f446,plain,(
% 1.36/0.53    ( ! [X19] : (k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X19)) = k10_relat_1(k6_relat_1(k1_relat_1(sK1)),X19)) )),
% 1.36/0.53    inference(forward_demodulation,[],[f445,f290])).
% 1.36/0.53  fof(f290,plain,(
% 1.36/0.53    k5_relat_1(sK1,k4_relat_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.36/0.53    inference(forward_demodulation,[],[f289,f116])).
% 1.36/0.53  fof(f116,plain,(
% 1.36/0.53    k2_funct_1(sK1) = k4_relat_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f115,f35])).
% 1.36/0.53  fof(f115,plain,(
% 1.36/0.53    k2_funct_1(sK1) = k4_relat_1(sK1) | ~v1_relat_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f113,f36])).
% 1.36/0.53  fof(f36,plain,(
% 1.36/0.53    v1_funct_1(sK1)),
% 1.36/0.53    inference(cnf_transformation,[],[f34])).
% 1.36/0.53  fof(f113,plain,(
% 1.36/0.53    k2_funct_1(sK1) = k4_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.36/0.53    inference(resolution,[],[f48,f37])).
% 1.36/0.53  fof(f37,plain,(
% 1.36/0.53    v2_funct_1(sK1)),
% 1.36/0.53    inference(cnf_transformation,[],[f34])).
% 1.36/0.53  fof(f48,plain,(
% 1.36/0.53    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f25])).
% 1.36/0.53  fof(f25,plain,(
% 1.36/0.53    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.53    inference(flattening,[],[f24])).
% 1.36/0.53  fof(f24,plain,(
% 1.36/0.53    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f10])).
% 1.36/0.53  fof(f10,axiom,(
% 1.36/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.36/0.53  fof(f289,plain,(
% 1.36/0.53    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))),
% 1.36/0.53    inference(subsumption_resolution,[],[f288,f35])).
% 1.36/0.53  fof(f288,plain,(
% 1.36/0.53    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.36/0.53    inference(subsumption_resolution,[],[f283,f36])).
% 1.36/0.53  fof(f283,plain,(
% 1.36/0.53    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.36/0.53    inference(resolution,[],[f49,f37])).
% 1.36/0.53  fof(f49,plain,(
% 1.36/0.53    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f27])).
% 1.36/0.53  fof(f27,plain,(
% 1.36/0.53    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.53    inference(flattening,[],[f26])).
% 1.36/0.53  fof(f26,plain,(
% 1.36/0.53    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f15])).
% 1.36/0.53  fof(f15,axiom,(
% 1.36/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.36/0.53  fof(f445,plain,(
% 1.36/0.53    ( ! [X19] : (k10_relat_1(k5_relat_1(sK1,k4_relat_1(sK1)),X19) = k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X19))) )),
% 1.36/0.53    inference(resolution,[],[f400,f35])).
% 1.36/0.53  fof(f400,plain,(
% 1.36/0.53    ( ! [X14,X15] : (~v1_relat_1(X14) | k10_relat_1(k5_relat_1(X14,k4_relat_1(sK1)),X15) = k10_relat_1(X14,k10_relat_1(k4_relat_1(sK1),X15))) )),
% 1.36/0.53    inference(resolution,[],[f57,f119])).
% 1.36/0.53  fof(f119,plain,(
% 1.36/0.53    v1_relat_1(k4_relat_1(sK1))),
% 1.36/0.53    inference(backward_demodulation,[],[f64,f116])).
% 1.36/0.53  fof(f64,plain,(
% 1.36/0.53    v1_relat_1(k2_funct_1(sK1))),
% 1.36/0.53    inference(subsumption_resolution,[],[f63,f35])).
% 1.36/0.53  fof(f63,plain,(
% 1.36/0.53    v1_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1)),
% 1.36/0.53    inference(resolution,[],[f46,f36])).
% 1.36/0.53  fof(f46,plain,(
% 1.36/0.53    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f23])).
% 1.36/0.53  fof(f23,plain,(
% 1.36/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.53    inference(flattening,[],[f22])).
% 1.36/0.53  fof(f22,plain,(
% 1.36/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.53    inference(ennf_transformation,[],[f11])).
% 1.36/0.53  fof(f11,axiom,(
% 1.36/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.36/0.53  fof(f57,plain,(
% 1.36/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f30])).
% 1.36/0.53  fof(f30,plain,(
% 1.36/0.53    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f6])).
% 1.36/0.53  fof(f6,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 1.36/0.53  fof(f513,plain,(
% 1.36/0.53    ( ! [X0] : (k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X0)))) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f512,f35])).
% 1.36/0.53  fof(f512,plain,(
% 1.36/0.53    ( ! [X0] : (k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X0))) | ~v1_relat_1(sK1)) )),
% 1.36/0.53    inference(subsumption_resolution,[],[f498,f36])).
% 1.36/0.53  fof(f498,plain,(
% 1.36/0.53    ( ! [X0] : (k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,k10_relat_1(sK1,k10_relat_1(k4_relat_1(sK1),X0))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.36/0.53    inference(resolution,[],[f58,f144])).
% 1.36/0.53  fof(f144,plain,(
% 1.36/0.53    ( ! [X3] : (r1_tarski(k10_relat_1(k4_relat_1(sK1),X3),k2_relat_1(sK1))) )),
% 1.36/0.53    inference(forward_demodulation,[],[f135,f81])).
% 1.36/0.53  fof(f81,plain,(
% 1.36/0.53    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))),
% 1.36/0.53    inference(resolution,[],[f43,f35])).
% 1.36/0.53  fof(f43,plain,(
% 1.36/0.53    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f20])).
% 1.36/0.53  fof(f20,plain,(
% 1.36/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.53    inference(ennf_transformation,[],[f8])).
% 1.36/0.53  fof(f8,axiom,(
% 1.36/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.36/0.53  fof(f135,plain,(
% 1.36/0.53    ( ! [X3] : (r1_tarski(k10_relat_1(k4_relat_1(sK1),X3),k1_relat_1(k4_relat_1(sK1)))) )),
% 1.36/0.53    inference(backward_demodulation,[],[f97,f116])).
% 1.36/0.53  fof(f97,plain,(
% 1.36/0.53    ( ! [X3] : (r1_tarski(k10_relat_1(k2_funct_1(sK1),X3),k1_relat_1(k2_funct_1(sK1)))) )),
% 1.36/0.53    inference(resolution,[],[f55,f64])).
% 1.36/0.53  fof(f55,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 1.36/0.53    inference(cnf_transformation,[],[f28])).
% 1.36/0.53  fof(f28,plain,(
% 1.36/0.53    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(ennf_transformation,[],[f5])).
% 1.36/0.53  fof(f5,axiom,(
% 1.36/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.36/0.53  fof(f58,plain,(
% 1.36/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.36/0.53    inference(cnf_transformation,[],[f32])).
% 1.36/0.53  fof(f32,plain,(
% 1.36/0.53    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.36/0.53    inference(flattening,[],[f31])).
% 1.36/0.53  fof(f31,plain,(
% 1.36/0.53    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.36/0.53    inference(ennf_transformation,[],[f13])).
% 1.36/0.53  fof(f13,axiom,(
% 1.36/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.36/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.36/0.53  fof(f118,plain,(
% 1.36/0.53    k9_relat_1(sK1,sK0) != k10_relat_1(k4_relat_1(sK1),sK0)),
% 1.36/0.53    inference(backward_demodulation,[],[f38,f116])).
% 1.36/0.53  fof(f38,plain,(
% 1.36/0.53    k9_relat_1(sK1,sK0) != k10_relat_1(k2_funct_1(sK1),sK0)),
% 1.36/0.53    inference(cnf_transformation,[],[f34])).
% 1.36/0.53  % SZS output end Proof for theBenchmark
% 1.36/0.53  % (12402)------------------------------
% 1.36/0.53  % (12402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (12402)Termination reason: Refutation
% 1.36/0.53  
% 1.36/0.53  % (12402)Memory used [KB]: 2430
% 1.36/0.53  % (12402)Time elapsed: 0.115 s
% 1.36/0.53  % (12402)------------------------------
% 1.36/0.53  % (12402)------------------------------
% 1.36/0.53  % (12387)Success in time 0.173 s
%------------------------------------------------------------------------------
