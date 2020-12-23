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
% DateTime   : Thu Dec  3 12:54:05 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   97 (1094 expanded)
%              Number of leaves         :   12 ( 281 expanded)
%              Depth                    :   22
%              Number of atoms          :  164 (2717 expanded)
%              Number of equality atoms :   82 ( 990 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3979,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3977])).

fof(f3977,plain,(
    k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f65,f3847])).

fof(f3847,plain,(
    ! [X14,X13] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X13),X14)) = k1_setfam_1(k2_tarski(X14,k9_relat_1(sK2,X13))) ),
    inference(backward_demodulation,[],[f3273,f3846])).

fof(f3846,plain,(
    ! [X10,X11] : k1_setfam_1(k2_tarski(X11,k9_relat_1(sK2,X10))) = k9_relat_1(k7_relat_1(sK2,X10),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X10),X11)))) ),
    inference(forward_demodulation,[],[f3845,f458])).

fof(f458,plain,(
    ! [X4,X3] : k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X3))),X4) = k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X3),X4))) ),
    inference(forward_demodulation,[],[f448,f82])).

fof(f82,plain,(
    ! [X2,X3] : k7_relat_1(k7_relat_1(sK2,X2),k10_relat_1(sK2,X3)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3)) ),
    inference(superposition,[],[f76,f63])).

fof(f63,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,X1))) ),
    inference(resolution,[],[f45,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f39,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f76,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(resolution,[],[f46,f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f40,f31])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f448,plain,(
    ! [X4,X3] : k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X3))),X4) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),k10_relat_1(sK2,X4))) ),
    inference(superposition,[],[f117,f63])).

fof(f117,plain,(
    ! [X8,X9] : k1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9)) = k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(sK2,X8)),X9)) ),
    inference(resolution,[],[f104,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f104,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[],[f93,f50])).

fof(f50,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0) ),
    inference(resolution,[],[f33,f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).

fof(f93,plain,(
    ! [X8,X9] : v1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9)) ),
    inference(subsumption_resolution,[],[f92,f27])).

fof(f92,plain,(
    ! [X8,X9] :
      ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f88,f28])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ! [X8,X9] :
      ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f37,f76])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f3845,plain,(
    ! [X10,X11] : k9_relat_1(k7_relat_1(sK2,X10),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X10))),X11)) = k1_setfam_1(k2_tarski(X11,k9_relat_1(sK2,X10))) ),
    inference(forward_demodulation,[],[f3825,f62])).

fof(f62,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(forward_demodulation,[],[f60,f54])).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) ),
    inference(resolution,[],[f42,f27])).

fof(f60,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0))) ),
    inference(resolution,[],[f43,f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f3825,plain,(
    ! [X10,X11] : k9_relat_1(k7_relat_1(sK2,X10),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X10))),X11)) = k1_setfam_1(k2_tarski(X11,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X10))))) ),
    inference(superposition,[],[f462,f463])).

fof(f463,plain,(
    ! [X2,X3] : k9_relat_1(k7_relat_1(sK2,X2),X3) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X2))),X3) ),
    inference(forward_demodulation,[],[f451,f122])).

fof(f122,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) = k9_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(backward_demodulation,[],[f89,f119])).

fof(f119,plain,(
    ! [X12,X13] : k9_relat_1(k7_relat_1(sK2,X12),X13) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X12),X13)) ),
    inference(resolution,[],[f104,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f89,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(backward_demodulation,[],[f84,f86])).

fof(f86,plain,(
    ! [X4,X5] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X4,X5))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X4),X5)) ),
    inference(superposition,[],[f48,f76])).

fof(f48,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f32,f27])).

fof(f84,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) ),
    inference(superposition,[],[f62,f76])).

fof(f451,plain,(
    ! [X2,X3] : k9_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3))) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X2))),X3) ),
    inference(superposition,[],[f123,f117])).

fof(f123,plain,(
    ! [X4,X5] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X4,X5))) = k9_relat_1(k7_relat_1(sK2,X4),X5) ),
    inference(backward_demodulation,[],[f86,f119])).

fof(f462,plain,(
    ! [X8,X7] : k9_relat_1(k7_relat_1(sK2,X7),k10_relat_1(k7_relat_1(sK2,X7),X8)) = k1_setfam_1(k2_tarski(X8,k9_relat_1(sK2,X7))) ),
    inference(forward_demodulation,[],[f461,f232])).

fof(f232,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(k7_relat_1(sK2,X0),X0) ),
    inference(forward_demodulation,[],[f229,f48])).

fof(f229,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(k7_relat_1(sK2,X0),X0) ),
    inference(superposition,[],[f119,f50])).

fof(f461,plain,(
    ! [X8,X7] : k9_relat_1(k7_relat_1(sK2,X7),k10_relat_1(k7_relat_1(sK2,X7),X8)) = k1_setfam_1(k2_tarski(X8,k9_relat_1(k7_relat_1(sK2,X7),X7))) ),
    inference(backward_demodulation,[],[f113,f460])).

fof(f460,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(forward_demodulation,[],[f450,f122])).

fof(f450,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) = k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(superposition,[],[f171,f117])).

fof(f171,plain,(
    ! [X2,X3] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X2,X3))) = k9_relat_1(k7_relat_1(sK2,X3),X2) ),
    inference(forward_demodulation,[],[f158,f119])).

fof(f158,plain,(
    ! [X2,X3] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X2,X3))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2)) ),
    inference(superposition,[],[f48,f78])).

fof(f78,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f76,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f113,plain,(
    ! [X8,X7] : k9_relat_1(k7_relat_1(sK2,X7),k10_relat_1(k7_relat_1(sK2,X7),X8)) = k1_setfam_1(k2_tarski(X8,k9_relat_1(k7_relat_1(sK2,X7),k1_relat_1(k7_relat_1(sK2,X7))))) ),
    inference(subsumption_resolution,[],[f109,f104])).

fof(f109,plain,(
    ! [X8,X7] :
      ( k9_relat_1(k7_relat_1(sK2,X7),k10_relat_1(k7_relat_1(sK2,X7),X8)) = k1_setfam_1(k2_tarski(X8,k9_relat_1(k7_relat_1(sK2,X7),k1_relat_1(k7_relat_1(sK2,X7)))))
      | ~ v1_relat_1(k7_relat_1(sK2,X7)) ) ),
    inference(resolution,[],[f44,f95])).

fof(f95,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[],[f91,f50])).

fof(f91,plain,(
    ! [X6,X7] : v1_funct_1(k7_relat_1(k7_relat_1(sK2,X6),X7)) ),
    inference(subsumption_resolution,[],[f90,f27])).

fof(f90,plain,(
    ! [X6,X7] :
      ( v1_funct_1(k7_relat_1(k7_relat_1(sK2,X6),X7))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f87,f28])).

fof(f87,plain,(
    ! [X6,X7] :
      ( v1_funct_1(k7_relat_1(k7_relat_1(sK2,X6),X7))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f38,f76])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f36,f31])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f3273,plain,(
    ! [X14,X13] : k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X13),X14)) = k9_relat_1(k7_relat_1(sK2,X13),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X13),X14)))) ),
    inference(forward_demodulation,[],[f3255,f197])).

fof(f197,plain,(
    ! [X2,X3] : k9_relat_1(k7_relat_1(sK2,X2),k10_relat_1(sK2,X3)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3)) ),
    inference(superposition,[],[f123,f63])).

fof(f3255,plain,(
    ! [X14,X13] : k9_relat_1(k7_relat_1(sK2,X13),k10_relat_1(sK2,X14)) = k9_relat_1(k7_relat_1(sK2,X13),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X13),X14)))) ),
    inference(superposition,[],[f121,f82])).

fof(f121,plain,(
    ! [X6,X7] : k9_relat_1(k7_relat_1(sK2,X6),X7) = k9_relat_1(k7_relat_1(sK2,X6),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X6),X7))) ),
    inference(backward_demodulation,[],[f116,f117])).

fof(f116,plain,(
    ! [X6,X7] : k9_relat_1(k7_relat_1(sK2,X6),X7) = k9_relat_1(k7_relat_1(sK2,X6),k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(sK2,X6)),X7))) ),
    inference(resolution,[],[f104,f43])).

fof(f65,plain,(
    k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(backward_demodulation,[],[f47,f63])).

fof(f47,plain,(
    k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0))) ),
    inference(backward_demodulation,[],[f41,f30])).

fof(f41,plain,(
    k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1)) ),
    inference(definition_unfolding,[],[f29,f31,f31])).

fof(f29,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:29:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.44  % (32694)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.44  % (32701)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.46  % (32700)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (32702)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.46  % (32707)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.46  % (32709)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.46  % (32699)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.46  % (32703)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.46  % (32696)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (32708)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.47  % (32693)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.47  % (32706)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.47  % (32697)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.48  % (32705)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.48  % (32695)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.48  % (32692)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.49  % (32704)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.50  % (32710)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.48/0.55  % (32702)Refutation found. Thanks to Tanya!
% 1.48/0.55  % SZS status Theorem for theBenchmark
% 1.48/0.55  % SZS output start Proof for theBenchmark
% 1.48/0.55  fof(f3979,plain,(
% 1.48/0.55    $false),
% 1.48/0.55    inference(trivial_inequality_removal,[],[f3977])).
% 1.48/0.55  fof(f3977,plain,(
% 1.48/0.55    k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0)))),
% 1.48/0.55    inference(superposition,[],[f65,f3847])).
% 1.48/0.55  fof(f3847,plain,(
% 1.48/0.55    ( ! [X14,X13] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X13),X14)) = k1_setfam_1(k2_tarski(X14,k9_relat_1(sK2,X13)))) )),
% 1.48/0.55    inference(backward_demodulation,[],[f3273,f3846])).
% 1.48/0.55  fof(f3846,plain,(
% 1.48/0.55    ( ! [X10,X11] : (k1_setfam_1(k2_tarski(X11,k9_relat_1(sK2,X10))) = k9_relat_1(k7_relat_1(sK2,X10),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X10),X11))))) )),
% 1.48/0.55    inference(forward_demodulation,[],[f3845,f458])).
% 1.48/0.55  fof(f458,plain,(
% 1.48/0.55    ( ! [X4,X3] : (k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X3))),X4) = k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X3),X4)))) )),
% 1.48/0.55    inference(forward_demodulation,[],[f448,f82])).
% 1.48/0.55  fof(f82,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK2,X2),k10_relat_1(sK2,X3)) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3))) )),
% 1.48/0.55    inference(superposition,[],[f76,f63])).
% 1.48/0.55  fof(f63,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,X1)))) )),
% 1.48/0.55    inference(resolution,[],[f45,f27])).
% 1.48/0.55  fof(f27,plain,(
% 1.48/0.55    v1_relat_1(sK2)),
% 1.48/0.55    inference(cnf_transformation,[],[f26])).
% 1.48/0.55  fof(f26,plain,(
% 1.48/0.55    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.48/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).
% 1.48/0.55  fof(f25,plain,(
% 1.48/0.55    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f14,plain,(
% 1.48/0.55    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.48/0.55    inference(flattening,[],[f13])).
% 1.48/0.55  fof(f13,plain,(
% 1.48/0.55    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.48/0.55    inference(ennf_transformation,[],[f12])).
% 1.48/0.55  fof(f12,negated_conjecture,(
% 1.48/0.55    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 1.48/0.55    inference(negated_conjecture,[],[f11])).
% 1.48/0.55  fof(f11,conjecture,(
% 1.48/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).
% 1.48/0.55  fof(f45,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 1.48/0.55    inference(definition_unfolding,[],[f39,f31])).
% 1.48/0.55  fof(f31,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f2])).
% 1.48/0.55  fof(f2,axiom,(
% 1.48/0.55    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.48/0.55  fof(f39,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f23])).
% 1.48/0.55  fof(f23,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.48/0.55    inference(ennf_transformation,[],[f9])).
% 1.48/0.55  fof(f9,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.48/0.55  fof(f76,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.48/0.55    inference(resolution,[],[f46,f27])).
% 1.48/0.55  fof(f46,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.48/0.55    inference(definition_unfolding,[],[f40,f31])).
% 1.48/0.55  fof(f40,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f24])).
% 1.48/0.55  fof(f24,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.48/0.55    inference(ennf_transformation,[],[f3])).
% 1.48/0.55  fof(f3,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 1.48/0.55  fof(f448,plain,(
% 1.48/0.55    ( ! [X4,X3] : (k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X3))),X4) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),k10_relat_1(sK2,X4)))) )),
% 1.48/0.55    inference(superposition,[],[f117,f63])).
% 1.48/0.55  fof(f117,plain,(
% 1.48/0.55    ( ! [X8,X9] : (k1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9)) = k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(sK2,X8)),X9))) )),
% 1.48/0.55    inference(resolution,[],[f104,f42])).
% 1.48/0.55  fof(f42,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 1.48/0.55    inference(definition_unfolding,[],[f34,f31])).
% 1.48/0.55  fof(f34,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f17])).
% 1.48/0.55  fof(f17,plain,(
% 1.48/0.55    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(ennf_transformation,[],[f7])).
% 1.48/0.55  fof(f7,axiom,(
% 1.48/0.55    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.48/0.55  fof(f104,plain,(
% 1.48/0.55    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 1.48/0.55    inference(superposition,[],[f93,f50])).
% 1.48/0.55  fof(f50,plain,(
% 1.48/0.55    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)) )),
% 1.48/0.55    inference(resolution,[],[f33,f27])).
% 1.48/0.55  fof(f33,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f16])).
% 1.48/0.55  fof(f16,plain,(
% 1.48/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(ennf_transformation,[],[f4])).
% 1.48/0.55  fof(f4,axiom,(
% 1.48/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).
% 1.48/0.55  fof(f93,plain,(
% 1.48/0.55    ( ! [X8,X9] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9))) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f92,f27])).
% 1.48/0.55  fof(f92,plain,(
% 1.48/0.55    ( ! [X8,X9] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9)) | ~v1_relat_1(sK2)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f88,f28])).
% 1.48/0.55  fof(f28,plain,(
% 1.48/0.55    v1_funct_1(sK2)),
% 1.48/0.55    inference(cnf_transformation,[],[f26])).
% 1.48/0.55  fof(f88,plain,(
% 1.48/0.55    ( ! [X8,X9] : (v1_relat_1(k7_relat_1(k7_relat_1(sK2,X8),X9)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.48/0.55    inference(superposition,[],[f37,f76])).
% 1.48/0.55  fof(f37,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f22])).
% 1.48/0.55  fof(f22,plain,(
% 1.48/0.55    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.55    inference(flattening,[],[f21])).
% 1.48/0.55  fof(f21,plain,(
% 1.48/0.55    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f8])).
% 1.48/0.55  fof(f8,axiom,(
% 1.48/0.55    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 1.48/0.55  fof(f3845,plain,(
% 1.48/0.55    ( ! [X10,X11] : (k9_relat_1(k7_relat_1(sK2,X10),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X10))),X11)) = k1_setfam_1(k2_tarski(X11,k9_relat_1(sK2,X10)))) )),
% 1.48/0.55    inference(forward_demodulation,[],[f3825,f62])).
% 1.48/0.55  fof(f62,plain,(
% 1.48/0.55    ( ! [X0] : (k9_relat_1(sK2,X0) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 1.48/0.55    inference(forward_demodulation,[],[f60,f54])).
% 1.48/0.55  fof(f54,plain,(
% 1.48/0.55    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0))) )),
% 1.48/0.55    inference(resolution,[],[f42,f27])).
% 1.48/0.55  fof(f60,plain,(
% 1.48/0.55    ( ! [X0] : (k9_relat_1(sK2,X0) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)))) )),
% 1.48/0.55    inference(resolution,[],[f43,f27])).
% 1.48/0.55  fof(f43,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)))) )),
% 1.48/0.55    inference(definition_unfolding,[],[f35,f31])).
% 1.48/0.55  fof(f35,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f18])).
% 1.48/0.55  fof(f18,plain,(
% 1.48/0.55    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(ennf_transformation,[],[f5])).
% 1.48/0.55  fof(f5,axiom,(
% 1.48/0.55    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 1.48/0.55  fof(f3825,plain,(
% 1.48/0.55    ( ! [X10,X11] : (k9_relat_1(k7_relat_1(sK2,X10),k10_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X10))),X11)) = k1_setfam_1(k2_tarski(X11,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X10)))))) )),
% 1.48/0.55    inference(superposition,[],[f462,f463])).
% 1.48/0.55  fof(f463,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k9_relat_1(k7_relat_1(sK2,X2),X3) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X2))),X3)) )),
% 1.48/0.55    inference(forward_demodulation,[],[f451,f122])).
% 1.48/0.55  fof(f122,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k9_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) = k9_relat_1(k7_relat_1(sK2,X0),X1)) )),
% 1.48/0.55    inference(backward_demodulation,[],[f89,f119])).
% 1.48/0.55  fof(f119,plain,(
% 1.48/0.55    ( ! [X12,X13] : (k9_relat_1(k7_relat_1(sK2,X12),X13) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X12),X13))) )),
% 1.48/0.55    inference(resolution,[],[f104,f32])).
% 1.48/0.55  fof(f32,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f15])).
% 1.48/0.55  fof(f15,plain,(
% 1.48/0.55    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(ennf_transformation,[],[f6])).
% 1.48/0.55  fof(f6,axiom,(
% 1.48/0.55    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.48/0.55  fof(f89,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k9_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 1.48/0.55    inference(backward_demodulation,[],[f84,f86])).
% 1.48/0.55  fof(f86,plain,(
% 1.48/0.55    ( ! [X4,X5] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X4,X5))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X4),X5))) )),
% 1.48/0.55    inference(superposition,[],[f48,f76])).
% 1.48/0.55  fof(f48,plain,(
% 1.48/0.55    ( ! [X0] : (k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 1.48/0.55    inference(resolution,[],[f32,f27])).
% 1.48/0.55  fof(f84,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)))) )),
% 1.48/0.55    inference(superposition,[],[f62,f76])).
% 1.48/0.55  fof(f451,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k9_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X3))) = k9_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X2))),X3)) )),
% 1.48/0.55    inference(superposition,[],[f123,f117])).
% 1.48/0.55  fof(f123,plain,(
% 1.48/0.55    ( ! [X4,X5] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X4,X5))) = k9_relat_1(k7_relat_1(sK2,X4),X5)) )),
% 1.48/0.55    inference(backward_demodulation,[],[f86,f119])).
% 1.48/0.55  fof(f462,plain,(
% 1.48/0.55    ( ! [X8,X7] : (k9_relat_1(k7_relat_1(sK2,X7),k10_relat_1(k7_relat_1(sK2,X7),X8)) = k1_setfam_1(k2_tarski(X8,k9_relat_1(sK2,X7)))) )),
% 1.48/0.55    inference(forward_demodulation,[],[f461,f232])).
% 1.48/0.55  fof(f232,plain,(
% 1.48/0.55    ( ! [X0] : (k9_relat_1(sK2,X0) = k9_relat_1(k7_relat_1(sK2,X0),X0)) )),
% 1.48/0.55    inference(forward_demodulation,[],[f229,f48])).
% 1.48/0.55  fof(f229,plain,(
% 1.48/0.55    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(k7_relat_1(sK2,X0),X0)) )),
% 1.48/0.55    inference(superposition,[],[f119,f50])).
% 1.48/0.55  fof(f461,plain,(
% 1.48/0.55    ( ! [X8,X7] : (k9_relat_1(k7_relat_1(sK2,X7),k10_relat_1(k7_relat_1(sK2,X7),X8)) = k1_setfam_1(k2_tarski(X8,k9_relat_1(k7_relat_1(sK2,X7),X7)))) )),
% 1.48/0.55    inference(backward_demodulation,[],[f113,f460])).
% 1.48/0.55  fof(f460,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 1.48/0.55    inference(forward_demodulation,[],[f450,f122])).
% 1.48/0.55  fof(f450,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k9_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) = k9_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 1.48/0.55    inference(superposition,[],[f171,f117])).
% 1.48/0.55  fof(f171,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X2,X3))) = k9_relat_1(k7_relat_1(sK2,X3),X2)) )),
% 1.48/0.55    inference(forward_demodulation,[],[f158,f119])).
% 1.48/0.55  fof(f158,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X2,X3))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X2))) )),
% 1.48/0.55    inference(superposition,[],[f48,f78])).
% 1.48/0.55  fof(f78,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_tarski(X1,X0)))) )),
% 1.48/0.55    inference(superposition,[],[f76,f30])).
% 1.48/0.55  fof(f30,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f1])).
% 1.48/0.55  fof(f1,axiom,(
% 1.48/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.48/0.55  fof(f113,plain,(
% 1.48/0.55    ( ! [X8,X7] : (k9_relat_1(k7_relat_1(sK2,X7),k10_relat_1(k7_relat_1(sK2,X7),X8)) = k1_setfam_1(k2_tarski(X8,k9_relat_1(k7_relat_1(sK2,X7),k1_relat_1(k7_relat_1(sK2,X7)))))) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f109,f104])).
% 1.48/0.55  fof(f109,plain,(
% 1.48/0.55    ( ! [X8,X7] : (k9_relat_1(k7_relat_1(sK2,X7),k10_relat_1(k7_relat_1(sK2,X7),X8)) = k1_setfam_1(k2_tarski(X8,k9_relat_1(k7_relat_1(sK2,X7),k1_relat_1(k7_relat_1(sK2,X7))))) | ~v1_relat_1(k7_relat_1(sK2,X7))) )),
% 1.48/0.55    inference(resolution,[],[f44,f95])).
% 1.48/0.55  fof(f95,plain,(
% 1.48/0.55    ( ! [X0] : (v1_funct_1(k7_relat_1(sK2,X0))) )),
% 1.48/0.55    inference(superposition,[],[f91,f50])).
% 1.48/0.55  fof(f91,plain,(
% 1.48/0.55    ( ! [X6,X7] : (v1_funct_1(k7_relat_1(k7_relat_1(sK2,X6),X7))) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f90,f27])).
% 1.48/0.55  fof(f90,plain,(
% 1.48/0.55    ( ! [X6,X7] : (v1_funct_1(k7_relat_1(k7_relat_1(sK2,X6),X7)) | ~v1_relat_1(sK2)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f87,f28])).
% 1.48/0.55  fof(f87,plain,(
% 1.48/0.55    ( ! [X6,X7] : (v1_funct_1(k7_relat_1(k7_relat_1(sK2,X6),X7)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.48/0.55    inference(superposition,[],[f38,f76])).
% 1.48/0.55  fof(f38,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f22])).
% 1.48/0.55  fof(f44,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 1.48/0.55    inference(definition_unfolding,[],[f36,f31])).
% 1.48/0.55  fof(f36,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f20])).
% 1.48/0.55  fof(f20,plain,(
% 1.48/0.55    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.48/0.55    inference(flattening,[],[f19])).
% 1.48/0.55  fof(f19,plain,(
% 1.48/0.55    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.48/0.55    inference(ennf_transformation,[],[f10])).
% 1.48/0.55  fof(f10,axiom,(
% 1.48/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.48/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 1.48/0.55  fof(f3273,plain,(
% 1.48/0.55    ( ! [X14,X13] : (k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X13),X14)) = k9_relat_1(k7_relat_1(sK2,X13),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X13),X14))))) )),
% 1.48/0.55    inference(forward_demodulation,[],[f3255,f197])).
% 1.48/0.55  fof(f197,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k9_relat_1(k7_relat_1(sK2,X2),k10_relat_1(sK2,X3)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X2),X3))) )),
% 1.48/0.55    inference(superposition,[],[f123,f63])).
% 1.48/0.55  fof(f3255,plain,(
% 1.48/0.55    ( ! [X14,X13] : (k9_relat_1(k7_relat_1(sK2,X13),k10_relat_1(sK2,X14)) = k9_relat_1(k7_relat_1(sK2,X13),k1_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X13),X14))))) )),
% 1.48/0.55    inference(superposition,[],[f121,f82])).
% 1.48/0.55  fof(f121,plain,(
% 1.48/0.55    ( ! [X6,X7] : (k9_relat_1(k7_relat_1(sK2,X6),X7) = k9_relat_1(k7_relat_1(sK2,X6),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X6),X7)))) )),
% 1.48/0.55    inference(backward_demodulation,[],[f116,f117])).
% 1.48/0.55  fof(f116,plain,(
% 1.48/0.55    ( ! [X6,X7] : (k9_relat_1(k7_relat_1(sK2,X6),X7) = k9_relat_1(k7_relat_1(sK2,X6),k1_setfam_1(k2_tarski(k1_relat_1(k7_relat_1(sK2,X6)),X7)))) )),
% 1.48/0.55    inference(resolution,[],[f104,f43])).
% 1.48/0.55  fof(f65,plain,(
% 1.48/0.55    k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0))) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))),
% 1.48/0.55    inference(backward_demodulation,[],[f47,f63])).
% 1.48/0.55  fof(f47,plain,(
% 1.48/0.55    k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0)))),
% 1.48/0.55    inference(backward_demodulation,[],[f41,f30])).
% 1.48/0.55  fof(f41,plain,(
% 1.48/0.55    k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))),
% 1.48/0.55    inference(definition_unfolding,[],[f29,f31,f31])).
% 1.48/0.55  fof(f29,plain,(
% 1.48/0.55    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 1.48/0.55    inference(cnf_transformation,[],[f26])).
% 1.48/0.55  % SZS output end Proof for theBenchmark
% 1.48/0.55  % (32702)------------------------------
% 1.48/0.55  % (32702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (32702)Termination reason: Refutation
% 1.48/0.55  
% 1.48/0.55  % (32702)Memory used [KB]: 13816
% 1.48/0.55  % (32702)Time elapsed: 0.151 s
% 1.48/0.55  % (32702)------------------------------
% 1.48/0.55  % (32702)------------------------------
% 1.48/0.55  % (32691)Success in time 0.202 s
%------------------------------------------------------------------------------
