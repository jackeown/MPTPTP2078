%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:05 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 353 expanded)
%              Number of leaves         :   11 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          :  133 ( 931 expanded)
%              Number of equality atoms :   63 ( 317 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f380])).

fof(f380,plain,(
    k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) != k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f39,f270])).

fof(f270,plain,(
    ! [X8,X9] : k9_relat_1(sK2,k3_xboole_0(X8,k10_relat_1(sK2,X9))) = k3_xboole_0(X9,k9_relat_1(sK2,X8)) ),
    inference(forward_demodulation,[],[f269,f131])).

fof(f131,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(sK2,k3_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f120,f49])).

fof(f49,plain,(
    ! [X3] : k9_relat_1(sK2,X3) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X3))) ),
    inference(forward_demodulation,[],[f43,f42])).

fof(f42,plain,(
    ! [X2] : k3_xboole_0(k1_relat_1(sK2),X2) = k1_relat_1(k7_relat_1(sK2,X2)) ),
    inference(resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).

fof(f43,plain,(
    ! [X3] : k9_relat_1(sK2,X3) = k9_relat_1(sK2,k3_xboole_0(k1_relat_1(sK2),X3)) ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f120,plain,(
    ! [X0] : k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f49,f102])).

fof(f102,plain,(
    ! [X2] : k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X2)) ),
    inference(subsumption_resolution,[],[f94,f26])).

fof(f94,plain,(
    ! [X2] :
      ( k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f41,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f41,plain,(
    ! [X1] : k7_relat_1(sK2,X1) = k7_relat_1(k7_relat_1(sK2,X1),X1) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).

fof(f269,plain,(
    ! [X8,X9] : k9_relat_1(sK2,k3_xboole_0(X8,k10_relat_1(sK2,X9))) = k3_xboole_0(X9,k9_relat_1(sK2,k3_xboole_0(X8,X8))) ),
    inference(forward_demodulation,[],[f267,f49])).

fof(f267,plain,(
    ! [X8,X9] : k9_relat_1(sK2,k3_xboole_0(X8,k10_relat_1(sK2,X9))) = k3_xboole_0(X9,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,k3_xboole_0(X8,X8))))) ),
    inference(backward_demodulation,[],[f107,f250])).

fof(f250,plain,(
    ! [X4,X5] : k1_relat_1(k7_relat_1(sK2,k3_xboole_0(X4,X5))) = k3_xboole_0(X5,k1_relat_1(k7_relat_1(sK2,X4))) ),
    inference(superposition,[],[f68,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f68,plain,(
    ! [X4,X5] : k3_xboole_0(k1_relat_1(k7_relat_1(sK2,X4)),X5) = k1_relat_1(k7_relat_1(sK2,k3_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f58,f48])).

fof(f48,plain,(
    ! [X10,X9] : k7_relat_1(k7_relat_1(sK2,X9),X10) = k7_relat_1(sK2,k3_xboole_0(X9,X10)) ),
    inference(resolution,[],[f26,f38])).

fof(f58,plain,(
    ! [X4,X5] : k3_xboole_0(k1_relat_1(k7_relat_1(sK2,X4)),X5) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X4),X5)) ),
    inference(resolution,[],[f51,f32])).

fof(f51,plain,(
    ! [X5] : v1_relat_1(k7_relat_1(sK2,X5)) ),
    inference(subsumption_resolution,[],[f45,f27])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X5] :
      ( v1_relat_1(k7_relat_1(sK2,X5))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f26,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f107,plain,(
    ! [X8,X9] : k3_xboole_0(X9,k9_relat_1(sK2,k3_xboole_0(X8,k1_relat_1(k7_relat_1(sK2,X8))))) = k9_relat_1(sK2,k3_xboole_0(X8,k10_relat_1(sK2,X9))) ),
    inference(backward_demodulation,[],[f74,f106])).

fof(f106,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k10_relat_1(sK2,X4)) = k3_xboole_0(X3,k3_xboole_0(X3,k10_relat_1(sK2,X4))) ),
    inference(forward_demodulation,[],[f105,f47])).

fof(f47,plain,(
    ! [X8,X7] : k10_relat_1(k7_relat_1(sK2,X7),X8) = k3_xboole_0(X7,k10_relat_1(sK2,X8)) ),
    inference(resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f105,plain,(
    ! [X4,X3] : k10_relat_1(k7_relat_1(sK2,X3),X4) = k3_xboole_0(X3,k10_relat_1(k7_relat_1(sK2,X3),X4)) ),
    inference(subsumption_resolution,[],[f96,f51])).

fof(f96,plain,(
    ! [X4,X3] :
      ( k10_relat_1(k7_relat_1(sK2,X3),X4) = k3_xboole_0(X3,k10_relat_1(k7_relat_1(sK2,X3),X4))
      | ~ v1_relat_1(k7_relat_1(sK2,X3)) ) ),
    inference(superposition,[],[f37,f41])).

fof(f74,plain,(
    ! [X8,X9] : k3_xboole_0(X9,k9_relat_1(sK2,k3_xboole_0(X8,k1_relat_1(k7_relat_1(sK2,X8))))) = k9_relat_1(sK2,k3_xboole_0(X8,k3_xboole_0(X8,k10_relat_1(sK2,X9)))) ),
    inference(forward_demodulation,[],[f73,f47])).

fof(f73,plain,(
    ! [X8,X9] : k3_xboole_0(X9,k9_relat_1(sK2,k3_xboole_0(X8,k1_relat_1(k7_relat_1(sK2,X8))))) = k9_relat_1(sK2,k3_xboole_0(X8,k10_relat_1(k7_relat_1(sK2,X8),X9))) ),
    inference(forward_demodulation,[],[f72,f66])).

fof(f66,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f65,f40])).

fof(f40,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f26,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f65,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f56,f48])).

fof(f56,plain,(
    ! [X0,X1] : k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1)) ),
    inference(resolution,[],[f51,f30])).

fof(f72,plain,(
    ! [X8,X9] : k9_relat_1(k7_relat_1(sK2,X8),k10_relat_1(k7_relat_1(sK2,X8),X9)) = k3_xboole_0(X9,k9_relat_1(sK2,k3_xboole_0(X8,k1_relat_1(k7_relat_1(sK2,X8))))) ),
    inference(forward_demodulation,[],[f71,f66])).

fof(f71,plain,(
    ! [X8,X9] : k9_relat_1(k7_relat_1(sK2,X8),k10_relat_1(k7_relat_1(sK2,X8),X9)) = k3_xboole_0(X9,k9_relat_1(k7_relat_1(sK2,X8),k1_relat_1(k7_relat_1(sK2,X8)))) ),
    inference(subsumption_resolution,[],[f60,f52])).

fof(f52,plain,(
    ! [X6] : v1_funct_1(k7_relat_1(sK2,X6)) ),
    inference(subsumption_resolution,[],[f46,f27])).

fof(f46,plain,(
    ! [X6] :
      ( v1_funct_1(k7_relat_1(sK2,X6))
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X8,X9] :
      ( k9_relat_1(k7_relat_1(sK2,X8),k10_relat_1(k7_relat_1(sK2,X8),X9)) = k3_xboole_0(X9,k9_relat_1(k7_relat_1(sK2,X8),k1_relat_1(k7_relat_1(sK2,X8))))
      | ~ v1_funct_1(k7_relat_1(sK2,X8)) ) ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f39,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f28,f29])).

fof(f28,plain,(
    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (21176)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (21174)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.49  % (21173)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (21175)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (21185)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.49  % (21184)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (21194)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (21175)Refutation not found, incomplete strategy% (21175)------------------------------
% 0.20/0.50  % (21175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21179)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (21186)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (21177)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (21191)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (21178)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (21195)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  % (21183)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (21175)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21175)Memory used [KB]: 10490
% 0.20/0.51  % (21175)Time elapsed: 0.094 s
% 0.20/0.51  % (21175)------------------------------
% 0.20/0.51  % (21175)------------------------------
% 0.20/0.51  % (21192)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (21190)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.24/0.51  % (21189)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.24/0.51  % (21187)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.24/0.51  % (21172)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.24/0.51  % (21181)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.24/0.52  % (21182)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.24/0.52  % (21182)Refutation not found, incomplete strategy% (21182)------------------------------
% 1.24/0.52  % (21182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (21182)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (21182)Memory used [KB]: 10618
% 1.24/0.52  % (21182)Time elapsed: 0.110 s
% 1.24/0.52  % (21182)------------------------------
% 1.24/0.52  % (21182)------------------------------
% 1.24/0.52  % (21183)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.24/0.52  fof(f383,plain,(
% 1.24/0.52    $false),
% 1.24/0.52    inference(trivial_inequality_removal,[],[f380])).
% 1.24/0.52  fof(f380,plain,(
% 1.24/0.52    k3_xboole_0(sK1,k9_relat_1(sK2,sK0)) != k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),
% 1.24/0.52    inference(superposition,[],[f39,f270])).
% 1.24/0.52  fof(f270,plain,(
% 1.24/0.52    ( ! [X8,X9] : (k9_relat_1(sK2,k3_xboole_0(X8,k10_relat_1(sK2,X9))) = k3_xboole_0(X9,k9_relat_1(sK2,X8))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f269,f131])).
% 1.24/0.52  fof(f131,plain,(
% 1.24/0.52    ( ! [X0] : (k9_relat_1(sK2,X0) = k9_relat_1(sK2,k3_xboole_0(X0,X0))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f120,f49])).
% 1.24/0.52  fof(f49,plain,(
% 1.24/0.52    ( ! [X3] : (k9_relat_1(sK2,X3) = k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X3)))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f43,f42])).
% 1.24/0.52  fof(f42,plain,(
% 1.24/0.52    ( ! [X2] : (k3_xboole_0(k1_relat_1(sK2),X2) = k1_relat_1(k7_relat_1(sK2,X2))) )),
% 1.24/0.52    inference(resolution,[],[f26,f32])).
% 1.24/0.52  fof(f32,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f16])).
% 1.24/0.52  fof(f16,plain,(
% 1.24/0.52    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(ennf_transformation,[],[f6])).
% 1.24/0.52  fof(f6,axiom,(
% 1.24/0.52    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.24/0.52  fof(f26,plain,(
% 1.24/0.52    v1_relat_1(sK2)),
% 1.24/0.52    inference(cnf_transformation,[],[f25])).
% 1.24/0.52  fof(f25,plain,(
% 1.24/0.52    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).
% 1.24/0.52  fof(f24,plain,(
% 1.24/0.52    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f13,plain,(
% 1.24/0.52    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.24/0.52    inference(flattening,[],[f12])).
% 1.24/0.52  fof(f12,plain,(
% 1.24/0.52    ? [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) != k3_xboole_0(k9_relat_1(X2,X0),X1) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.24/0.52    inference(ennf_transformation,[],[f11])).
% 1.24/0.52  fof(f11,negated_conjecture,(
% 1.24/0.52    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 1.24/0.52    inference(negated_conjecture,[],[f10])).
% 1.24/0.52  fof(f10,conjecture,(
% 1.24/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).
% 1.24/0.52  fof(f43,plain,(
% 1.24/0.52    ( ! [X3] : (k9_relat_1(sK2,X3) = k9_relat_1(sK2,k3_xboole_0(k1_relat_1(sK2),X3))) )),
% 1.24/0.52    inference(resolution,[],[f26,f33])).
% 1.24/0.52  fof(f33,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f17])).
% 1.24/0.52  fof(f17,plain,(
% 1.24/0.52    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(ennf_transformation,[],[f4])).
% 1.24/0.52  fof(f4,axiom,(
% 1.24/0.52    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).
% 1.24/0.52  fof(f120,plain,(
% 1.24/0.52    ( ! [X0] : (k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) = k9_relat_1(sK2,k3_xboole_0(X0,X0))) )),
% 1.24/0.52    inference(superposition,[],[f49,f102])).
% 1.24/0.52  fof(f102,plain,(
% 1.24/0.52    ( ! [X2] : (k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X2))) )),
% 1.24/0.52    inference(subsumption_resolution,[],[f94,f26])).
% 1.24/0.52  fof(f94,plain,(
% 1.24/0.52    ( ! [X2] : (k7_relat_1(sK2,X2) = k7_relat_1(sK2,k3_xboole_0(X2,X2)) | ~v1_relat_1(sK2)) )),
% 1.24/0.52    inference(superposition,[],[f41,f38])).
% 1.24/0.52  fof(f38,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f23])).
% 1.24/0.52  fof(f23,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.24/0.52    inference(ennf_transformation,[],[f2])).
% 1.24/0.52  fof(f2,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.24/0.52  fof(f41,plain,(
% 1.24/0.52    ( ! [X1] : (k7_relat_1(sK2,X1) = k7_relat_1(k7_relat_1(sK2,X1),X1)) )),
% 1.24/0.52    inference(resolution,[],[f26,f31])).
% 1.24/0.52  fof(f31,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f15])).
% 1.24/0.52  fof(f15,plain,(
% 1.24/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(ennf_transformation,[],[f3])).
% 1.24/0.52  fof(f3,axiom,(
% 1.24/0.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).
% 1.24/0.52  fof(f269,plain,(
% 1.24/0.52    ( ! [X8,X9] : (k9_relat_1(sK2,k3_xboole_0(X8,k10_relat_1(sK2,X9))) = k3_xboole_0(X9,k9_relat_1(sK2,k3_xboole_0(X8,X8)))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f267,f49])).
% 1.24/0.52  fof(f267,plain,(
% 1.24/0.52    ( ! [X8,X9] : (k9_relat_1(sK2,k3_xboole_0(X8,k10_relat_1(sK2,X9))) = k3_xboole_0(X9,k9_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,k3_xboole_0(X8,X8)))))) )),
% 1.24/0.52    inference(backward_demodulation,[],[f107,f250])).
% 1.24/0.52  fof(f250,plain,(
% 1.24/0.52    ( ! [X4,X5] : (k1_relat_1(k7_relat_1(sK2,k3_xboole_0(X4,X5))) = k3_xboole_0(X5,k1_relat_1(k7_relat_1(sK2,X4)))) )),
% 1.24/0.52    inference(superposition,[],[f68,f29])).
% 1.24/0.52  fof(f29,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f1])).
% 1.24/0.52  fof(f1,axiom,(
% 1.24/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.24/0.52  fof(f68,plain,(
% 1.24/0.52    ( ! [X4,X5] : (k3_xboole_0(k1_relat_1(k7_relat_1(sK2,X4)),X5) = k1_relat_1(k7_relat_1(sK2,k3_xboole_0(X4,X5)))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f58,f48])).
% 1.24/0.52  fof(f48,plain,(
% 1.24/0.52    ( ! [X10,X9] : (k7_relat_1(k7_relat_1(sK2,X9),X10) = k7_relat_1(sK2,k3_xboole_0(X9,X10))) )),
% 1.24/0.52    inference(resolution,[],[f26,f38])).
% 1.24/0.52  fof(f58,plain,(
% 1.24/0.52    ( ! [X4,X5] : (k3_xboole_0(k1_relat_1(k7_relat_1(sK2,X4)),X5) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X4),X5))) )),
% 1.24/0.52    inference(resolution,[],[f51,f32])).
% 1.24/0.52  fof(f51,plain,(
% 1.24/0.52    ( ! [X5] : (v1_relat_1(k7_relat_1(sK2,X5))) )),
% 1.24/0.52    inference(subsumption_resolution,[],[f45,f27])).
% 1.24/0.52  fof(f27,plain,(
% 1.24/0.52    v1_funct_1(sK2)),
% 1.24/0.52    inference(cnf_transformation,[],[f25])).
% 1.24/0.52  fof(f45,plain,(
% 1.24/0.52    ( ! [X5] : (v1_relat_1(k7_relat_1(sK2,X5)) | ~v1_funct_1(sK2)) )),
% 1.24/0.52    inference(resolution,[],[f26,f35])).
% 1.24/0.52  fof(f35,plain,(
% 1.24/0.52    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f21])).
% 1.24/0.52  fof(f21,plain,(
% 1.24/0.52    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.24/0.52    inference(flattening,[],[f20])).
% 1.24/0.52  fof(f20,plain,(
% 1.24/0.52    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f7])).
% 1.24/0.52  fof(f7,axiom,(
% 1.24/0.52    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 1.24/0.52  fof(f107,plain,(
% 1.24/0.52    ( ! [X8,X9] : (k3_xboole_0(X9,k9_relat_1(sK2,k3_xboole_0(X8,k1_relat_1(k7_relat_1(sK2,X8))))) = k9_relat_1(sK2,k3_xboole_0(X8,k10_relat_1(sK2,X9)))) )),
% 1.24/0.52    inference(backward_demodulation,[],[f74,f106])).
% 1.24/0.52  fof(f106,plain,(
% 1.24/0.52    ( ! [X4,X3] : (k3_xboole_0(X3,k10_relat_1(sK2,X4)) = k3_xboole_0(X3,k3_xboole_0(X3,k10_relat_1(sK2,X4)))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f105,f47])).
% 1.24/0.52  fof(f47,plain,(
% 1.24/0.52    ( ! [X8,X7] : (k10_relat_1(k7_relat_1(sK2,X7),X8) = k3_xboole_0(X7,k10_relat_1(sK2,X8))) )),
% 1.24/0.52    inference(resolution,[],[f26,f37])).
% 1.24/0.52  fof(f37,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f22])).
% 1.24/0.52  fof(f22,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.24/0.52    inference(ennf_transformation,[],[f8])).
% 1.24/0.52  fof(f8,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.24/0.52  fof(f105,plain,(
% 1.24/0.52    ( ! [X4,X3] : (k10_relat_1(k7_relat_1(sK2,X3),X4) = k3_xboole_0(X3,k10_relat_1(k7_relat_1(sK2,X3),X4))) )),
% 1.24/0.52    inference(subsumption_resolution,[],[f96,f51])).
% 1.24/0.52  fof(f96,plain,(
% 1.24/0.52    ( ! [X4,X3] : (k10_relat_1(k7_relat_1(sK2,X3),X4) = k3_xboole_0(X3,k10_relat_1(k7_relat_1(sK2,X3),X4)) | ~v1_relat_1(k7_relat_1(sK2,X3))) )),
% 1.24/0.52    inference(superposition,[],[f37,f41])).
% 1.24/0.52  fof(f74,plain,(
% 1.24/0.52    ( ! [X8,X9] : (k3_xboole_0(X9,k9_relat_1(sK2,k3_xboole_0(X8,k1_relat_1(k7_relat_1(sK2,X8))))) = k9_relat_1(sK2,k3_xboole_0(X8,k3_xboole_0(X8,k10_relat_1(sK2,X9))))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f73,f47])).
% 1.24/0.52  fof(f73,plain,(
% 1.24/0.52    ( ! [X8,X9] : (k3_xboole_0(X9,k9_relat_1(sK2,k3_xboole_0(X8,k1_relat_1(k7_relat_1(sK2,X8))))) = k9_relat_1(sK2,k3_xboole_0(X8,k10_relat_1(k7_relat_1(sK2,X8),X9)))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f72,f66])).
% 1.24/0.52  fof(f66,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k9_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f65,f40])).
% 1.24/0.52  fof(f40,plain,(
% 1.24/0.52    ( ! [X0] : (k9_relat_1(sK2,X0) = k2_relat_1(k7_relat_1(sK2,X0))) )),
% 1.24/0.52    inference(resolution,[],[f26,f30])).
% 1.24/0.52  fof(f30,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f14])).
% 1.24/0.52  fof(f14,plain,(
% 1.24/0.52    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(ennf_transformation,[],[f5])).
% 1.24/0.52  fof(f5,axiom,(
% 1.24/0.52    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.24/0.52  fof(f65,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(sK2,k3_xboole_0(X0,X1)))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f56,f48])).
% 1.24/0.52  fof(f56,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK2,X0),X1) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0),X1))) )),
% 1.24/0.52    inference(resolution,[],[f51,f30])).
% 1.24/0.52  fof(f72,plain,(
% 1.24/0.52    ( ! [X8,X9] : (k9_relat_1(k7_relat_1(sK2,X8),k10_relat_1(k7_relat_1(sK2,X8),X9)) = k3_xboole_0(X9,k9_relat_1(sK2,k3_xboole_0(X8,k1_relat_1(k7_relat_1(sK2,X8)))))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f71,f66])).
% 1.24/0.52  fof(f71,plain,(
% 1.24/0.52    ( ! [X8,X9] : (k9_relat_1(k7_relat_1(sK2,X8),k10_relat_1(k7_relat_1(sK2,X8),X9)) = k3_xboole_0(X9,k9_relat_1(k7_relat_1(sK2,X8),k1_relat_1(k7_relat_1(sK2,X8))))) )),
% 1.24/0.52    inference(subsumption_resolution,[],[f60,f52])).
% 1.24/0.52  fof(f52,plain,(
% 1.24/0.52    ( ! [X6] : (v1_funct_1(k7_relat_1(sK2,X6))) )),
% 1.24/0.52    inference(subsumption_resolution,[],[f46,f27])).
% 1.24/0.52  fof(f46,plain,(
% 1.24/0.52    ( ! [X6] : (v1_funct_1(k7_relat_1(sK2,X6)) | ~v1_funct_1(sK2)) )),
% 1.24/0.52    inference(resolution,[],[f26,f36])).
% 1.24/0.52  fof(f36,plain,(
% 1.24/0.52    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f21])).
% 1.24/0.52  fof(f60,plain,(
% 1.24/0.52    ( ! [X8,X9] : (k9_relat_1(k7_relat_1(sK2,X8),k10_relat_1(k7_relat_1(sK2,X8),X9)) = k3_xboole_0(X9,k9_relat_1(k7_relat_1(sK2,X8),k1_relat_1(k7_relat_1(sK2,X8)))) | ~v1_funct_1(k7_relat_1(sK2,X8))) )),
% 1.24/0.52    inference(resolution,[],[f51,f34])).
% 1.24/0.52  fof(f34,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f19])).
% 1.24/0.52  fof(f19,plain,(
% 1.24/0.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.24/0.52    inference(flattening,[],[f18])).
% 1.24/0.52  fof(f18,plain,(
% 1.24/0.52    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.24/0.52    inference(ennf_transformation,[],[f9])).
% 1.24/0.52  fof(f9,axiom,(
% 1.24/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 1.24/0.52  fof(f39,plain,(
% 1.24/0.52    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(sK1,k9_relat_1(sK2,sK0))),
% 1.24/0.52    inference(forward_demodulation,[],[f28,f29])).
% 1.24/0.52  fof(f28,plain,(
% 1.24/0.52    k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k3_xboole_0(k9_relat_1(sK2,sK0),sK1)),
% 1.24/0.52    inference(cnf_transformation,[],[f25])).
% 1.24/0.52  % SZS output end Proof for theBenchmark
% 1.24/0.52  % (21183)------------------------------
% 1.24/0.52  % (21183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (21183)Termination reason: Refutation
% 1.24/0.52  
% 1.24/0.52  % (21183)Memory used [KB]: 1918
% 1.24/0.52  % (21183)Time elapsed: 0.119 s
% 1.24/0.52  % (21183)------------------------------
% 1.24/0.52  % (21183)------------------------------
% 1.24/0.52  % (21171)Success in time 0.163 s
%------------------------------------------------------------------------------
