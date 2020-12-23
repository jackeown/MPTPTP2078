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
% DateTime   : Thu Dec  3 12:53:57 EST 2020

% Result     : Theorem 6.17s
% Output     : Refutation 6.17s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 732 expanded)
%              Number of leaves         :   13 ( 195 expanded)
%              Depth                    :   24
%              Number of atoms          :  188 (1459 expanded)
%              Number of equality atoms :   80 ( 603 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10589,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10588,f34])).

fof(f34,plain,(
    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f10588,plain,(
    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f10552,f105])).

fof(f105,plain,(
    sK0 = k6_subset_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f71,f104])).

fof(f104,plain,(
    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f101,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f101,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,k2_relat_1(sK1)),sK0)
    | k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1)) ),
    inference(superposition,[],[f54,f71])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_subset_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f71,plain,(
    sK0 = k6_subset_1(sK0,k6_subset_1(sK0,k2_relat_1(sK1))) ),
    inference(resolution,[],[f33,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f38,f37,f37])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f33,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f10552,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k6_subset_1(sK0,k1_xboole_0) ),
    inference(superposition,[],[f2986,f10441])).

fof(f10441,plain,(
    k1_xboole_0 = k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(trivial_inequality_removal,[],[f10374])).

fof(f10374,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f236,f10296])).

fof(f10296,plain,(
    ! [X12] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12)))) ),
    inference(subsumption_resolution,[],[f10295,f293])).

fof(f293,plain,(
    ! [X10,X11] : r1_tarski(k10_relat_1(sK1,k6_subset_1(X10,X11)),k10_relat_1(sK1,X10)) ),
    inference(superposition,[],[f51,f64])).

fof(f64,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f62,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f32,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f10295,plain,(
    ! [X12] :
      ( ~ r1_tarski(k10_relat_1(sK1,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12)))),k10_relat_1(sK1,X12))
      | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12)))) ) ),
    inference(forward_demodulation,[],[f10200,f3567])).

fof(f3567,plain,(
    ! [X20] : k10_relat_1(sK1,X20) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X20))) ),
    inference(forward_demodulation,[],[f3566,f818])).

fof(f818,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k6_subset_1(k10_relat_1(sK1,X7),k10_relat_1(sK1,k6_subset_1(X7,k9_relat_1(sK1,k10_relat_1(sK1,X7))))) ),
    inference(forward_demodulation,[],[f814,f64])).

fof(f814,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k6_subset_1(k10_relat_1(sK1,X7),k6_subset_1(k10_relat_1(sK1,X7),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X7))))) ),
    inference(resolution,[],[f166,f53])).

fof(f166,plain,(
    ! [X4] : r1_tarski(k10_relat_1(sK1,X4),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X4)))) ),
    inference(resolution,[],[f60,f61])).

fof(f61,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) ),
    inference(resolution,[],[f31,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f60,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | r1_tarski(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1))) ) ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f3566,plain,(
    ! [X20] : k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X20))) = k6_subset_1(k10_relat_1(sK1,X20),k10_relat_1(sK1,k6_subset_1(X20,k9_relat_1(sK1,k10_relat_1(sK1,X20))))) ),
    inference(forward_demodulation,[],[f3565,f1388])).

fof(f1388,plain,(
    ! [X1] : k10_relat_1(sK1,X1) = k10_relat_1(sK1,k6_subset_1(X1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1346,f1158])).

fof(f1158,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k6_subset_1(k10_relat_1(sK1,X7),k1_xboole_0) ),
    inference(backward_demodulation,[],[f77,f1156])).

fof(f1156,plain,(
    ! [X9] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X9),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1153,f51])).

fof(f1153,plain,(
    ! [X9] :
      ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,X9),k1_relat_1(sK1)),k10_relat_1(sK1,X9))
      | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X9),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f54,f77])).

fof(f77,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k6_subset_1(k10_relat_1(sK1,X7),k6_subset_1(k10_relat_1(sK1,X7),k1_relat_1(sK1))) ),
    inference(resolution,[],[f61,f53])).

fof(f1346,plain,(
    ! [X1] : k6_subset_1(k10_relat_1(sK1,X1),k1_xboole_0) = k10_relat_1(sK1,k6_subset_1(X1,k1_xboole_0)) ),
    inference(superposition,[],[f64,f1271])).

fof(f1271,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f421,f1270])).

fof(f1270,plain,(
    ! [X8] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X8)) ),
    inference(forward_demodulation,[],[f1260,f1192])).

fof(f1192,plain,(
    ! [X6] : k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,k10_relat_1(sK1,X6))) ),
    inference(resolution,[],[f1163,f53])).

fof(f1163,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,k10_relat_1(sK1,X2)) ),
    inference(superposition,[],[f51,f1156])).

fof(f1260,plain,(
    ! [X8] : k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X8)) = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,k10_relat_1(sK1,X8))) ),
    inference(superposition,[],[f52,f1158])).

fof(f52,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f50,f50])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f421,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f420,f187])).

fof(f187,plain,(
    k1_xboole_0 = k6_subset_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f184,f51])).

fof(f184,plain,
    ( ~ r1_tarski(k6_subset_1(k1_xboole_0,sK0),k1_xboole_0)
    | k1_xboole_0 = k6_subset_1(k1_xboole_0,sK0) ),
    inference(superposition,[],[f54,f123])).

fof(f123,plain,(
    k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f117,f53])).

fof(f117,plain,(
    r1_tarski(k1_xboole_0,sK0) ),
    inference(superposition,[],[f51,f104])).

fof(f420,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k6_subset_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f417,f64])).

fof(f417,plain,(
    k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f409,f53])).

fof(f409,plain,(
    r1_tarski(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f293,f104])).

fof(f3565,plain,(
    ! [X20] : k6_subset_1(k10_relat_1(sK1,X20),k10_relat_1(sK1,k6_subset_1(X20,k9_relat_1(sK1,k10_relat_1(sK1,X20))))) = k10_relat_1(sK1,k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X20)),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f3492,f64])).

fof(f3492,plain,(
    ! [X20] : k6_subset_1(k10_relat_1(sK1,X20),k10_relat_1(sK1,k6_subset_1(X20,k9_relat_1(sK1,k10_relat_1(sK1,X20))))) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X20))),k10_relat_1(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f294,f3011])).

fof(f3011,plain,(
    ! [X11] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X11)),X11) ),
    inference(subsumption_resolution,[],[f3001,f51])).

fof(f3001,plain,(
    ! [X11] :
      ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X11)),X11),k9_relat_1(sK1,k10_relat_1(sK1,X11)))
      | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X11)),X11) ) ),
    inference(superposition,[],[f54,f82])).

fof(f82,plain,(
    ! [X6] : k9_relat_1(sK1,k10_relat_1(sK1,X6)) = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X6)),k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X6)),X6)) ),
    inference(resolution,[],[f65,f53])).

fof(f65,plain,(
    ! [X2] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2) ),
    inference(subsumption_resolution,[],[f63,f31])).

fof(f63,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK1)
      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2) ) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f294,plain,(
    ! [X6,X7] : k6_subset_1(k10_relat_1(sK1,X6),k10_relat_1(sK1,k6_subset_1(X6,X7))) = k6_subset_1(k10_relat_1(sK1,X7),k10_relat_1(sK1,k6_subset_1(X7,X6))) ),
    inference(forward_demodulation,[],[f291,f64])).

fof(f291,plain,(
    ! [X6,X7] : k6_subset_1(k10_relat_1(sK1,X7),k6_subset_1(k10_relat_1(sK1,X7),k10_relat_1(sK1,X6))) = k6_subset_1(k10_relat_1(sK1,X6),k10_relat_1(sK1,k6_subset_1(X6,X7))) ),
    inference(superposition,[],[f52,f64])).

fof(f10200,plain,(
    ! [X12] :
      ( ~ r1_tarski(k10_relat_1(sK1,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12)))),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X12))))
      | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12)))) ) ),
    inference(superposition,[],[f289,f2986])).

fof(f289,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k10_relat_1(sK1,X3),k10_relat_1(sK1,k6_subset_1(X2,X3)))
      | k1_xboole_0 = k10_relat_1(sK1,X3) ) ),
    inference(superposition,[],[f54,f64])).

fof(f236,plain,(
    ! [X2] :
      ( k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(sK0,X2))
      | k1_xboole_0 = k6_subset_1(sK0,X2) ) ),
    inference(resolution,[],[f59,f88])).

fof(f88,plain,(
    ! [X2] : r1_tarski(k6_subset_1(sK0,X2),k2_relat_1(sK1)) ),
    inference(resolution,[],[f67,f51])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f33,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | k1_xboole_0 = X0
      | k1_xboole_0 != k10_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 != k10_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f2986,plain,(
    ! [X2] : k9_relat_1(sK1,k10_relat_1(sK1,X2)) = k6_subset_1(X2,k6_subset_1(X2,k9_relat_1(sK1,k10_relat_1(sK1,X2)))) ),
    inference(superposition,[],[f82,f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:16:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (13915)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (13911)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.51  % (13907)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (13903)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.51  % (13899)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (13897)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.20/0.52  % (13901)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.20/0.53  % (13919)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.20/0.53  % (13905)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.20/0.53  % (13900)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.20/0.53  % (13895)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.20/0.53  % (13896)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.20/0.53  % (13920)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.54  % (13921)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.37/0.54  % (13898)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.37/0.54  % (13893)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.37/0.54  % (13894)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.37/0.54  % (13918)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.37/0.54  % (13922)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.55  % (13910)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.37/0.55  % (13913)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.37/0.55  % (13914)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.55  % (13902)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.55  % (13917)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.55  % (13906)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.37/0.55  % (13904)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.55  % (13912)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.37/0.56  % (13909)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.37/0.56  % (13908)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.37/0.57  % (13916)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 3.42/0.81  % (13895)Time limit reached!
% 3.42/0.81  % (13895)------------------------------
% 3.42/0.81  % (13895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.81  % (13895)Termination reason: Time limit
% 3.42/0.81  % (13895)Termination phase: Saturation
% 3.42/0.81  
% 3.42/0.81  % (13895)Memory used [KB]: 6780
% 3.42/0.81  % (13895)Time elapsed: 0.400 s
% 3.42/0.81  % (13895)------------------------------
% 3.42/0.81  % (13895)------------------------------
% 3.64/0.84  % (13917)Time limit reached!
% 3.64/0.84  % (13917)------------------------------
% 3.64/0.84  % (13917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.64/0.84  % (13917)Termination reason: Time limit
% 3.64/0.84  
% 3.64/0.84  % (13917)Memory used [KB]: 13048
% 3.64/0.84  % (13917)Time elapsed: 0.421 s
% 3.64/0.84  % (13917)------------------------------
% 3.64/0.84  % (13917)------------------------------
% 3.64/0.93  % (13922)Time limit reached!
% 3.64/0.93  % (13922)------------------------------
% 3.64/0.93  % (13922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.64/0.93  % (13922)Termination reason: Time limit
% 3.64/0.93  
% 3.64/0.93  % (13922)Memory used [KB]: 1918
% 3.64/0.93  % (13922)Time elapsed: 0.509 s
% 3.64/0.93  % (13922)------------------------------
% 3.64/0.93  % (13922)------------------------------
% 4.43/0.95  % (13899)Time limit reached!
% 4.43/0.95  % (13899)------------------------------
% 4.43/0.95  % (13899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.95  % (13899)Termination reason: Time limit
% 4.43/0.95  % (13899)Termination phase: Saturation
% 4.43/0.95  
% 4.43/0.95  % (13899)Memory used [KB]: 14967
% 4.43/0.95  % (13899)Time elapsed: 0.500 s
% 4.43/0.95  % (13899)------------------------------
% 4.43/0.95  % (13899)------------------------------
% 4.43/0.96  % (13923)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.43/0.97  % (13907)Time limit reached!
% 4.43/0.97  % (13907)------------------------------
% 4.43/0.97  % (13907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.97  % (13907)Termination reason: Time limit
% 4.43/0.97  % (13907)Termination phase: Saturation
% 4.43/0.97  
% 4.43/0.97  % (13907)Memory used [KB]: 6524
% 4.43/0.97  % (13907)Time elapsed: 0.500 s
% 4.43/0.97  % (13907)------------------------------
% 4.43/0.97  % (13907)------------------------------
% 4.43/0.97  % (13924)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.89/1.02  % (13900)Time limit reached!
% 4.89/1.02  % (13900)------------------------------
% 4.89/1.02  % (13900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.04  % (13900)Termination reason: Time limit
% 4.89/1.04  
% 4.89/1.04  % (13900)Memory used [KB]: 6780
% 4.89/1.04  % (13900)Time elapsed: 0.609 s
% 4.89/1.04  % (13900)------------------------------
% 4.89/1.04  % (13900)------------------------------
% 5.34/1.07  % (13925)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 5.58/1.10  % (13926)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.58/1.11  % (13927)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 6.17/1.17  % (13928)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.17/1.20  % (13910)Refutation found. Thanks to Tanya!
% 6.17/1.20  % SZS status Theorem for theBenchmark
% 6.17/1.21  % SZS output start Proof for theBenchmark
% 6.17/1.21  fof(f10589,plain,(
% 6.17/1.21    $false),
% 6.17/1.21    inference(subsumption_resolution,[],[f10588,f34])).
% 6.17/1.21  fof(f34,plain,(
% 6.17/1.21    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 6.17/1.21    inference(cnf_transformation,[],[f17])).
% 6.17/1.21  fof(f17,plain,(
% 6.17/1.21    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 6.17/1.21    inference(flattening,[],[f16])).
% 6.17/1.21  fof(f16,plain,(
% 6.17/1.21    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 6.17/1.21    inference(ennf_transformation,[],[f15])).
% 6.17/1.21  fof(f15,negated_conjecture,(
% 6.17/1.21    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 6.17/1.21    inference(negated_conjecture,[],[f14])).
% 6.17/1.21  fof(f14,conjecture,(
% 6.17/1.21    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 6.17/1.21  fof(f10588,plain,(
% 6.17/1.21    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 6.17/1.21    inference(forward_demodulation,[],[f10552,f105])).
% 6.17/1.21  fof(f105,plain,(
% 6.17/1.21    sK0 = k6_subset_1(sK0,k1_xboole_0)),
% 6.17/1.21    inference(backward_demodulation,[],[f71,f104])).
% 6.17/1.21  fof(f104,plain,(
% 6.17/1.21    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1))),
% 6.17/1.21    inference(subsumption_resolution,[],[f101,f51])).
% 6.17/1.21  fof(f51,plain,(
% 6.17/1.21    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 6.17/1.21    inference(definition_unfolding,[],[f35,f37])).
% 6.17/1.21  fof(f37,plain,(
% 6.17/1.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 6.17/1.21    inference(cnf_transformation,[],[f8])).
% 6.17/1.21  fof(f8,axiom,(
% 6.17/1.21    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 6.17/1.21  fof(f35,plain,(
% 6.17/1.21    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.17/1.21    inference(cnf_transformation,[],[f5])).
% 6.17/1.21  fof(f5,axiom,(
% 6.17/1.21    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.17/1.21  fof(f101,plain,(
% 6.17/1.21    ~r1_tarski(k6_subset_1(sK0,k2_relat_1(sK1)),sK0) | k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1))),
% 6.17/1.21    inference(superposition,[],[f54,f71])).
% 6.17/1.21  fof(f54,plain,(
% 6.17/1.21    ( ! [X0,X1] : (~r1_tarski(X0,k6_subset_1(X1,X0)) | k1_xboole_0 = X0) )),
% 6.17/1.21    inference(definition_unfolding,[],[f43,f37])).
% 6.17/1.21  fof(f43,plain,(
% 6.17/1.21    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 6.17/1.21    inference(cnf_transformation,[],[f24])).
% 6.17/1.21  fof(f24,plain,(
% 6.17/1.21    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 6.17/1.21    inference(ennf_transformation,[],[f6])).
% 6.17/1.21  fof(f6,axiom,(
% 6.17/1.21    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 6.17/1.21  fof(f71,plain,(
% 6.17/1.21    sK0 = k6_subset_1(sK0,k6_subset_1(sK0,k2_relat_1(sK1)))),
% 6.17/1.21    inference(resolution,[],[f33,f53])).
% 6.17/1.21  fof(f53,plain,(
% 6.17/1.21    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0) )),
% 6.17/1.21    inference(definition_unfolding,[],[f42,f50])).
% 6.17/1.21  fof(f50,plain,(
% 6.17/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 6.17/1.21    inference(definition_unfolding,[],[f38,f37,f37])).
% 6.17/1.21  fof(f38,plain,(
% 6.17/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.17/1.21    inference(cnf_transformation,[],[f7])).
% 6.17/1.21  fof(f7,axiom,(
% 6.17/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.17/1.21  fof(f42,plain,(
% 6.17/1.21    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 6.17/1.21    inference(cnf_transformation,[],[f23])).
% 6.17/1.21  fof(f23,plain,(
% 6.17/1.21    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.17/1.21    inference(ennf_transformation,[],[f4])).
% 6.17/1.21  fof(f4,axiom,(
% 6.17/1.21    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.17/1.21  fof(f33,plain,(
% 6.17/1.21    r1_tarski(sK0,k2_relat_1(sK1))),
% 6.17/1.21    inference(cnf_transformation,[],[f17])).
% 6.17/1.21  fof(f10552,plain,(
% 6.17/1.21    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k6_subset_1(sK0,k1_xboole_0)),
% 6.17/1.21    inference(superposition,[],[f2986,f10441])).
% 6.17/1.21  fof(f10441,plain,(
% 6.17/1.21    k1_xboole_0 = k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 6.17/1.21    inference(trivial_inequality_removal,[],[f10374])).
% 6.17/1.21  fof(f10374,plain,(
% 6.17/1.21    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 6.17/1.21    inference(superposition,[],[f236,f10296])).
% 6.17/1.21  fof(f10296,plain,(
% 6.17/1.21    ( ! [X12] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12))))) )),
% 6.17/1.21    inference(subsumption_resolution,[],[f10295,f293])).
% 6.17/1.21  fof(f293,plain,(
% 6.17/1.21    ( ! [X10,X11] : (r1_tarski(k10_relat_1(sK1,k6_subset_1(X10,X11)),k10_relat_1(sK1,X10))) )),
% 6.17/1.21    inference(superposition,[],[f51,f64])).
% 6.17/1.21  fof(f64,plain,(
% 6.17/1.21    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 6.17/1.21    inference(subsumption_resolution,[],[f62,f31])).
% 6.17/1.21  fof(f31,plain,(
% 6.17/1.21    v1_relat_1(sK1)),
% 6.17/1.21    inference(cnf_transformation,[],[f17])).
% 6.17/1.21  fof(f62,plain,(
% 6.17/1.21    ( ! [X0,X1] : (~v1_relat_1(sK1) | k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 6.17/1.21    inference(resolution,[],[f32,f48])).
% 6.17/1.21  fof(f48,plain,(
% 6.17/1.21    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 6.17/1.21    inference(cnf_transformation,[],[f28])).
% 6.17/1.21  fof(f28,plain,(
% 6.17/1.21    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 6.17/1.21    inference(flattening,[],[f27])).
% 6.17/1.21  fof(f27,plain,(
% 6.17/1.21    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 6.17/1.21    inference(ennf_transformation,[],[f11])).
% 6.17/1.21  fof(f11,axiom,(
% 6.17/1.21    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 6.17/1.21  fof(f32,plain,(
% 6.17/1.21    v1_funct_1(sK1)),
% 6.17/1.21    inference(cnf_transformation,[],[f17])).
% 6.17/1.21  fof(f10295,plain,(
% 6.17/1.21    ( ! [X12] : (~r1_tarski(k10_relat_1(sK1,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12)))),k10_relat_1(sK1,X12)) | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12))))) )),
% 6.17/1.21    inference(forward_demodulation,[],[f10200,f3567])).
% 6.17/1.21  fof(f3567,plain,(
% 6.17/1.21    ( ! [X20] : (k10_relat_1(sK1,X20) = k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X20)))) )),
% 6.17/1.21    inference(forward_demodulation,[],[f3566,f818])).
% 6.17/1.21  fof(f818,plain,(
% 6.17/1.21    ( ! [X7] : (k10_relat_1(sK1,X7) = k6_subset_1(k10_relat_1(sK1,X7),k10_relat_1(sK1,k6_subset_1(X7,k9_relat_1(sK1,k10_relat_1(sK1,X7)))))) )),
% 6.17/1.21    inference(forward_demodulation,[],[f814,f64])).
% 6.17/1.21  fof(f814,plain,(
% 6.17/1.21    ( ! [X7] : (k10_relat_1(sK1,X7) = k6_subset_1(k10_relat_1(sK1,X7),k6_subset_1(k10_relat_1(sK1,X7),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X7)))))) )),
% 6.17/1.21    inference(resolution,[],[f166,f53])).
% 6.17/1.21  fof(f166,plain,(
% 6.17/1.21    ( ! [X4] : (r1_tarski(k10_relat_1(sK1,X4),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X4))))) )),
% 6.17/1.21    inference(resolution,[],[f60,f61])).
% 6.17/1.21  fof(f61,plain,(
% 6.17/1.21    ( ! [X2] : (r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))) )),
% 6.17/1.21    inference(resolution,[],[f31,f39])).
% 6.17/1.21  fof(f39,plain,(
% 6.17/1.21    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 6.17/1.21    inference(cnf_transformation,[],[f18])).
% 6.17/1.21  fof(f18,plain,(
% 6.17/1.21    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.17/1.21    inference(ennf_transformation,[],[f9])).
% 6.17/1.21  fof(f9,axiom,(
% 6.17/1.21    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 6.17/1.21  fof(f60,plain,(
% 6.17/1.21    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | r1_tarski(X1,k10_relat_1(sK1,k9_relat_1(sK1,X1)))) )),
% 6.17/1.21    inference(resolution,[],[f31,f40])).
% 6.17/1.21  fof(f40,plain,(
% 6.17/1.21    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 6.17/1.21    inference(cnf_transformation,[],[f20])).
% 6.17/1.21  fof(f20,plain,(
% 6.17/1.21    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.17/1.21    inference(flattening,[],[f19])).
% 6.17/1.21  fof(f19,plain,(
% 6.17/1.21    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 6.17/1.21    inference(ennf_transformation,[],[f13])).
% 6.17/1.21  fof(f13,axiom,(
% 6.17/1.21    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 6.17/1.21  fof(f3566,plain,(
% 6.17/1.21    ( ! [X20] : (k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X20))) = k6_subset_1(k10_relat_1(sK1,X20),k10_relat_1(sK1,k6_subset_1(X20,k9_relat_1(sK1,k10_relat_1(sK1,X20)))))) )),
% 6.17/1.21    inference(forward_demodulation,[],[f3565,f1388])).
% 6.17/1.21  fof(f1388,plain,(
% 6.17/1.21    ( ! [X1] : (k10_relat_1(sK1,X1) = k10_relat_1(sK1,k6_subset_1(X1,k1_xboole_0))) )),
% 6.17/1.21    inference(forward_demodulation,[],[f1346,f1158])).
% 6.17/1.21  fof(f1158,plain,(
% 6.17/1.21    ( ! [X7] : (k10_relat_1(sK1,X7) = k6_subset_1(k10_relat_1(sK1,X7),k1_xboole_0)) )),
% 6.17/1.21    inference(backward_demodulation,[],[f77,f1156])).
% 6.17/1.21  fof(f1156,plain,(
% 6.17/1.21    ( ! [X9] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X9),k1_relat_1(sK1))) )),
% 6.17/1.21    inference(subsumption_resolution,[],[f1153,f51])).
% 6.17/1.21  fof(f1153,plain,(
% 6.17/1.21    ( ! [X9] : (~r1_tarski(k6_subset_1(k10_relat_1(sK1,X9),k1_relat_1(sK1)),k10_relat_1(sK1,X9)) | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X9),k1_relat_1(sK1))) )),
% 6.17/1.21    inference(superposition,[],[f54,f77])).
% 6.17/1.21  fof(f77,plain,(
% 6.17/1.21    ( ! [X7] : (k10_relat_1(sK1,X7) = k6_subset_1(k10_relat_1(sK1,X7),k6_subset_1(k10_relat_1(sK1,X7),k1_relat_1(sK1)))) )),
% 6.17/1.21    inference(resolution,[],[f61,f53])).
% 6.17/1.21  fof(f1346,plain,(
% 6.17/1.21    ( ! [X1] : (k6_subset_1(k10_relat_1(sK1,X1),k1_xboole_0) = k10_relat_1(sK1,k6_subset_1(X1,k1_xboole_0))) )),
% 6.17/1.21    inference(superposition,[],[f64,f1271])).
% 6.17/1.21  fof(f1271,plain,(
% 6.17/1.21    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 6.17/1.21    inference(backward_demodulation,[],[f421,f1270])).
% 6.17/1.21  fof(f1270,plain,(
% 6.17/1.21    ( ! [X8] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X8))) )),
% 6.17/1.21    inference(forward_demodulation,[],[f1260,f1192])).
% 6.17/1.21  fof(f1192,plain,(
% 6.17/1.21    ( ! [X6] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,k10_relat_1(sK1,X6)))) )),
% 6.17/1.21    inference(resolution,[],[f1163,f53])).
% 6.17/1.21  fof(f1163,plain,(
% 6.17/1.21    ( ! [X2] : (r1_tarski(k1_xboole_0,k10_relat_1(sK1,X2))) )),
% 6.17/1.21    inference(superposition,[],[f51,f1156])).
% 6.17/1.21  fof(f1260,plain,(
% 6.17/1.21    ( ! [X8] : (k6_subset_1(k10_relat_1(sK1,X8),k10_relat_1(sK1,X8)) = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,k10_relat_1(sK1,X8)))) )),
% 6.17/1.21    inference(superposition,[],[f52,f1158])).
% 6.17/1.21  fof(f52,plain,(
% 6.17/1.21    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 6.17/1.21    inference(definition_unfolding,[],[f36,f50,f50])).
% 6.17/1.21  fof(f36,plain,(
% 6.17/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.17/1.21    inference(cnf_transformation,[],[f1])).
% 6.17/1.21  fof(f1,axiom,(
% 6.17/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.17/1.21  fof(f421,plain,(
% 6.17/1.21    k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k1_xboole_0))),
% 6.17/1.21    inference(forward_demodulation,[],[f420,f187])).
% 6.17/1.21  fof(f187,plain,(
% 6.17/1.21    k1_xboole_0 = k6_subset_1(k1_xboole_0,sK0)),
% 6.17/1.21    inference(subsumption_resolution,[],[f184,f51])).
% 6.17/1.21  fof(f184,plain,(
% 6.17/1.21    ~r1_tarski(k6_subset_1(k1_xboole_0,sK0),k1_xboole_0) | k1_xboole_0 = k6_subset_1(k1_xboole_0,sK0)),
% 6.17/1.21    inference(superposition,[],[f54,f123])).
% 6.17/1.21  fof(f123,plain,(
% 6.17/1.21    k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,sK0))),
% 6.17/1.21    inference(resolution,[],[f117,f53])).
% 6.17/1.21  fof(f117,plain,(
% 6.17/1.21    r1_tarski(k1_xboole_0,sK0)),
% 6.17/1.21    inference(superposition,[],[f51,f104])).
% 6.17/1.21  fof(f420,plain,(
% 6.17/1.21    k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k6_subset_1(k1_xboole_0,sK0)))),
% 6.17/1.21    inference(forward_demodulation,[],[f417,f64])).
% 6.17/1.21  fof(f417,plain,(
% 6.17/1.21    k10_relat_1(sK1,k1_xboole_0) = k6_subset_1(k10_relat_1(sK1,k1_xboole_0),k6_subset_1(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,sK0)))),
% 6.17/1.21    inference(resolution,[],[f409,f53])).
% 6.17/1.21  fof(f409,plain,(
% 6.17/1.21    r1_tarski(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,sK0))),
% 6.17/1.21    inference(superposition,[],[f293,f104])).
% 6.17/1.21  fof(f3565,plain,(
% 6.17/1.21    ( ! [X20] : (k6_subset_1(k10_relat_1(sK1,X20),k10_relat_1(sK1,k6_subset_1(X20,k9_relat_1(sK1,k10_relat_1(sK1,X20))))) = k10_relat_1(sK1,k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X20)),k1_xboole_0))) )),
% 6.17/1.21    inference(forward_demodulation,[],[f3492,f64])).
% 6.17/1.21  fof(f3492,plain,(
% 6.17/1.21    ( ! [X20] : (k6_subset_1(k10_relat_1(sK1,X20),k10_relat_1(sK1,k6_subset_1(X20,k9_relat_1(sK1,k10_relat_1(sK1,X20))))) = k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X20))),k10_relat_1(sK1,k1_xboole_0))) )),
% 6.17/1.21    inference(superposition,[],[f294,f3011])).
% 6.17/1.21  fof(f3011,plain,(
% 6.17/1.21    ( ! [X11] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X11)),X11)) )),
% 6.17/1.21    inference(subsumption_resolution,[],[f3001,f51])).
% 6.17/1.21  fof(f3001,plain,(
% 6.17/1.21    ( ! [X11] : (~r1_tarski(k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X11)),X11),k9_relat_1(sK1,k10_relat_1(sK1,X11))) | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X11)),X11)) )),
% 6.17/1.21    inference(superposition,[],[f54,f82])).
% 6.17/1.21  fof(f82,plain,(
% 6.17/1.21    ( ! [X6] : (k9_relat_1(sK1,k10_relat_1(sK1,X6)) = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X6)),k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X6)),X6))) )),
% 6.17/1.21    inference(resolution,[],[f65,f53])).
% 6.17/1.21  fof(f65,plain,(
% 6.17/1.21    ( ! [X2] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2)) )),
% 6.17/1.21    inference(subsumption_resolution,[],[f63,f31])).
% 6.17/1.21  fof(f63,plain,(
% 6.17/1.21    ( ! [X2] : (~v1_relat_1(sK1) | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X2)),X2)) )),
% 6.17/1.21    inference(resolution,[],[f32,f44])).
% 6.17/1.21  fof(f44,plain,(
% 6.17/1.21    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 6.17/1.21    inference(cnf_transformation,[],[f26])).
% 6.17/1.21  fof(f26,plain,(
% 6.17/1.21    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.17/1.21    inference(flattening,[],[f25])).
% 6.17/1.21  fof(f25,plain,(
% 6.17/1.21    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.17/1.21    inference(ennf_transformation,[],[f12])).
% 6.17/1.21  fof(f12,axiom,(
% 6.17/1.21    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 6.17/1.21  fof(f294,plain,(
% 6.17/1.21    ( ! [X6,X7] : (k6_subset_1(k10_relat_1(sK1,X6),k10_relat_1(sK1,k6_subset_1(X6,X7))) = k6_subset_1(k10_relat_1(sK1,X7),k10_relat_1(sK1,k6_subset_1(X7,X6)))) )),
% 6.17/1.21    inference(forward_demodulation,[],[f291,f64])).
% 6.17/1.21  fof(f291,plain,(
% 6.17/1.21    ( ! [X6,X7] : (k6_subset_1(k10_relat_1(sK1,X7),k6_subset_1(k10_relat_1(sK1,X7),k10_relat_1(sK1,X6))) = k6_subset_1(k10_relat_1(sK1,X6),k10_relat_1(sK1,k6_subset_1(X6,X7)))) )),
% 6.17/1.21    inference(superposition,[],[f52,f64])).
% 6.17/1.21  fof(f10200,plain,(
% 6.17/1.21    ( ! [X12] : (~r1_tarski(k10_relat_1(sK1,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12)))),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X12)))) | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X12,k9_relat_1(sK1,k10_relat_1(sK1,X12))))) )),
% 6.17/1.21    inference(superposition,[],[f289,f2986])).
% 6.17/1.21  fof(f289,plain,(
% 6.17/1.21    ( ! [X2,X3] : (~r1_tarski(k10_relat_1(sK1,X3),k10_relat_1(sK1,k6_subset_1(X2,X3))) | k1_xboole_0 = k10_relat_1(sK1,X3)) )),
% 6.17/1.21    inference(superposition,[],[f54,f64])).
% 6.17/1.21  fof(f236,plain,(
% 6.17/1.21    ( ! [X2] : (k1_xboole_0 != k10_relat_1(sK1,k6_subset_1(sK0,X2)) | k1_xboole_0 = k6_subset_1(sK0,X2)) )),
% 6.17/1.21    inference(resolution,[],[f59,f88])).
% 6.17/1.21  fof(f88,plain,(
% 6.17/1.21    ( ! [X2] : (r1_tarski(k6_subset_1(sK0,X2),k2_relat_1(sK1))) )),
% 6.17/1.21    inference(resolution,[],[f67,f51])).
% 6.17/1.21  fof(f67,plain,(
% 6.17/1.21    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,k2_relat_1(sK1))) )),
% 6.17/1.21    inference(resolution,[],[f33,f49])).
% 6.17/1.21  fof(f49,plain,(
% 6.17/1.21    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 6.17/1.21    inference(cnf_transformation,[],[f30])).
% 6.17/1.21  fof(f30,plain,(
% 6.17/1.21    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 6.17/1.21    inference(flattening,[],[f29])).
% 6.17/1.21  fof(f29,plain,(
% 6.17/1.21    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 6.17/1.21    inference(ennf_transformation,[],[f3])).
% 6.17/1.21  fof(f3,axiom,(
% 6.17/1.21    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 6.17/1.21  fof(f59,plain,(
% 6.17/1.21    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k1_xboole_0 = X0 | k1_xboole_0 != k10_relat_1(sK1,X0)) )),
% 6.17/1.21    inference(resolution,[],[f31,f41])).
% 6.17/1.21  fof(f41,plain,(
% 6.17/1.21    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 != k10_relat_1(X1,X0)) )),
% 6.17/1.21    inference(cnf_transformation,[],[f22])).
% 6.17/1.21  fof(f22,plain,(
% 6.17/1.21    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 6.17/1.21    inference(flattening,[],[f21])).
% 6.17/1.21  fof(f21,plain,(
% 6.17/1.21    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 6.17/1.21    inference(ennf_transformation,[],[f10])).
% 6.17/1.21  fof(f10,axiom,(
% 6.17/1.21    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 6.17/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 6.17/1.21  fof(f2986,plain,(
% 6.17/1.21    ( ! [X2] : (k9_relat_1(sK1,k10_relat_1(sK1,X2)) = k6_subset_1(X2,k6_subset_1(X2,k9_relat_1(sK1,k10_relat_1(sK1,X2))))) )),
% 6.17/1.21    inference(superposition,[],[f82,f52])).
% 6.17/1.21  % SZS output end Proof for theBenchmark
% 6.17/1.21  % (13910)------------------------------
% 6.17/1.21  % (13910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.17/1.21  % (13910)Termination reason: Refutation
% 6.17/1.21  
% 6.17/1.21  % (13910)Memory used [KB]: 6396
% 6.17/1.21  % (13910)Time elapsed: 0.794 s
% 6.17/1.21  % (13910)------------------------------
% 6.17/1.21  % (13910)------------------------------
% 6.17/1.21  % (13892)Success in time 0.847 s
%------------------------------------------------------------------------------
