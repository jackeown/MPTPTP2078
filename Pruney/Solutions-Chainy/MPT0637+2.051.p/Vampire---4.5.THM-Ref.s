%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:29 EST 2020

% Result     : Theorem 3.75s
% Output     : Refutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 247 expanded)
%              Number of leaves         :   14 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  137 ( 389 expanded)
%              Number of equality atoms :   56 ( 162 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5204,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f5203])).

fof(f5203,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f43,f3668])).

fof(f3668,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f90,f3667])).

fof(f3667,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(forward_demodulation,[],[f3648,f300])).

fof(f300,plain,(
    ! [X17,X18] : k6_relat_1(k3_xboole_0(X17,X18)) = k8_relat_1(X17,k6_relat_1(k3_xboole_0(X17,X18))) ),
    inference(forward_demodulation,[],[f299,f45])).

fof(f45,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f299,plain,(
    ! [X17,X18] : k8_relat_1(X17,k6_relat_1(k3_xboole_0(X17,X18))) = k4_relat_1(k6_relat_1(k3_xboole_0(X17,X18))) ),
    inference(superposition,[],[f162,f141])).

fof(f141,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(k3_xboole_0(X1,X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f107,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f106,f90])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f104,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ) ),
    inference(resolution,[],[f62,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f162,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f161,f90])).

fof(f161,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f160,f90])).

fof(f160,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f158,f45])).

fof(f158,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f112,f44])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f110,f45])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f49,f44])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f3648,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1))) ),
    inference(resolution,[],[f267,f1606])).

fof(f1606,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) ),
    inference(resolution,[],[f199,f92])).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f80,f90])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1)) ),
    inference(resolution,[],[f61,f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f199,plain,(
    ! [X35,X33,X34] :
      ( ~ r1_tarski(k8_relat_1(X33,k6_relat_1(X34)),k6_relat_1(X35))
      | r1_tarski(k1_relat_1(k8_relat_1(X33,k6_relat_1(X34))),X35) ) ),
    inference(resolution,[],[f144,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,k6_relat_1(X1))
      | r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f95,f46])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_relat_1(X1))
      | r1_tarski(k1_relat_1(X0),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f50,f44])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f144,plain,(
    ! [X0,X1] : v1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[],[f73,f103])).

fof(f103,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(X1,X0)) ),
    inference(forward_demodulation,[],[f101,f46])).

fof(f101,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0)) ),
    inference(resolution,[],[f59,f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f57,f44])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f267,plain,(
    ! [X28,X26,X27] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X26,k6_relat_1(X27))),X28)
      | k8_relat_1(X26,k6_relat_1(X27)) = k8_relat_1(X26,k6_relat_1(k3_xboole_0(X28,X27))) ) ),
    inference(backward_demodulation,[],[f197,f266])).

fof(f266,plain,(
    ! [X39,X41,X40] : k5_relat_1(k6_relat_1(X41),k8_relat_1(X40,k6_relat_1(X39))) = k8_relat_1(X40,k6_relat_1(k3_xboole_0(X41,X39))) ),
    inference(backward_demodulation,[],[f207,f265])).

fof(f265,plain,(
    ! [X2,X3,X1] : k8_relat_1(X3,k6_relat_1(k3_xboole_0(X1,X2))) = k4_relat_1(k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3)))) ),
    inference(superposition,[],[f162,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X2)) ),
    inference(resolution,[],[f67,f44])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(f207,plain,(
    ! [X39,X41,X40] : k5_relat_1(k6_relat_1(X41),k8_relat_1(X40,k6_relat_1(X39))) = k4_relat_1(k8_relat_1(X41,k8_relat_1(X39,k6_relat_1(X40)))) ),
    inference(forward_demodulation,[],[f206,f193])).

fof(f193,plain,(
    ! [X14,X15,X16] : k8_relat_1(X14,k8_relat_1(X15,k6_relat_1(X16))) = k5_relat_1(k8_relat_1(X15,k6_relat_1(X16)),k6_relat_1(X14)) ),
    inference(resolution,[],[f144,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f206,plain,(
    ! [X39,X41,X40] : k4_relat_1(k5_relat_1(k8_relat_1(X39,k6_relat_1(X40)),k6_relat_1(X41))) = k5_relat_1(k6_relat_1(X41),k8_relat_1(X40,k6_relat_1(X39))) ),
    inference(forward_demodulation,[],[f201,f162])).

fof(f201,plain,(
    ! [X39,X41,X40] : k4_relat_1(k5_relat_1(k8_relat_1(X39,k6_relat_1(X40)),k6_relat_1(X41))) = k5_relat_1(k6_relat_1(X41),k4_relat_1(k8_relat_1(X39,k6_relat_1(X40)))) ),
    inference(resolution,[],[f144,f112])).

fof(f197,plain,(
    ! [X28,X26,X27] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X26,k6_relat_1(X27))),X28)
      | k8_relat_1(X26,k6_relat_1(X27)) = k5_relat_1(k6_relat_1(X28),k8_relat_1(X26,k6_relat_1(X27))) ) ),
    inference(resolution,[],[f144,f62])).

fof(f90,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f58,f44])).

fof(f43,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f39])).

fof(f39,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.54  % (15250)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (15248)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (15234)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.56  % (15238)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (15238)Refutation not found, incomplete strategy% (15238)------------------------------
% 0.20/0.56  % (15238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (15238)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (15238)Memory used [KB]: 6140
% 0.20/0.56  % (15238)Time elapsed: 0.135 s
% 0.20/0.56  % (15238)------------------------------
% 0.20/0.56  % (15238)------------------------------
% 0.20/0.56  % (15237)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (15227)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.56  % (15254)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.56  % (15237)Refutation not found, incomplete strategy% (15237)------------------------------
% 0.20/0.56  % (15237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (15237)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (15237)Memory used [KB]: 10618
% 0.20/0.56  % (15237)Time elapsed: 0.134 s
% 0.20/0.56  % (15237)------------------------------
% 0.20/0.56  % (15237)------------------------------
% 0.20/0.56  % (15236)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.57  % (15231)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.57  % (15242)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.58  % (15251)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.58  % (15243)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.58  % (15243)Refutation not found, incomplete strategy% (15243)------------------------------
% 0.20/0.58  % (15243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (15243)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (15243)Memory used [KB]: 10618
% 0.20/0.58  % (15243)Time elapsed: 0.162 s
% 0.20/0.58  % (15243)------------------------------
% 0.20/0.58  % (15243)------------------------------
% 0.20/0.58  % (15251)Refutation not found, incomplete strategy% (15251)------------------------------
% 0.20/0.58  % (15251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (15251)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (15251)Memory used [KB]: 10618
% 0.20/0.58  % (15251)Time elapsed: 0.108 s
% 0.20/0.58  % (15251)------------------------------
% 0.20/0.58  % (15251)------------------------------
% 0.20/0.58  % (15247)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.58  % (15254)Refutation not found, incomplete strategy% (15254)------------------------------
% 0.20/0.58  % (15254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (15254)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (15254)Memory used [KB]: 6140
% 0.20/0.58  % (15254)Time elapsed: 0.153 s
% 0.20/0.58  % (15254)------------------------------
% 0.20/0.58  % (15254)------------------------------
% 0.20/0.58  % (15232)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.59  % (15228)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.59  % (15228)Refutation not found, incomplete strategy% (15228)------------------------------
% 0.20/0.59  % (15228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (15228)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (15228)Memory used [KB]: 1663
% 0.20/0.59  % (15228)Time elapsed: 0.162 s
% 0.20/0.59  % (15228)------------------------------
% 0.20/0.59  % (15228)------------------------------
% 0.20/0.59  % (15229)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.59  % (15233)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.59  % (15230)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.59  % (15253)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.59  % (15246)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.60  % (15252)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.68/0.60  % (15241)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.68/0.60  % (15255)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.68/0.60  % (15241)Refutation not found, incomplete strategy% (15241)------------------------------
% 1.68/0.60  % (15241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (15241)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.60  
% 1.68/0.60  % (15241)Memory used [KB]: 1663
% 1.68/0.60  % (15241)Time elapsed: 0.172 s
% 1.68/0.60  % (15241)------------------------------
% 1.68/0.60  % (15241)------------------------------
% 1.68/0.60  % (15235)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.68/0.60  % (15256)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.68/0.60  % (15245)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.68/0.60  % (15245)Refutation not found, incomplete strategy% (15245)------------------------------
% 1.68/0.60  % (15245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.60  % (15240)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.68/0.60  % (15239)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.68/0.60  % (15245)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.60  
% 1.68/0.60  % (15245)Memory used [KB]: 1663
% 1.68/0.60  % (15245)Time elapsed: 0.175 s
% 1.68/0.60  % (15245)------------------------------
% 1.68/0.60  % (15245)------------------------------
% 1.68/0.60  % (15255)Refutation not found, incomplete strategy% (15255)------------------------------
% 1.68/0.60  % (15255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.61  % (15239)Refutation not found, incomplete strategy% (15239)------------------------------
% 1.68/0.61  % (15239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.61  % (15244)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.68/0.61  % (15239)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.61  
% 1.68/0.61  % (15239)Memory used [KB]: 10618
% 1.68/0.61  % (15239)Time elapsed: 0.185 s
% 1.68/0.61  % (15252)Refutation not found, incomplete strategy% (15252)------------------------------
% 1.68/0.61  % (15252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.61  % (15252)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.61  
% 1.68/0.61  % (15252)Memory used [KB]: 6140
% 1.68/0.61  % (15252)Time elapsed: 0.190 s
% 1.68/0.61  % (15252)------------------------------
% 1.68/0.61  % (15252)------------------------------
% 1.68/0.61  % (15239)------------------------------
% 1.68/0.61  % (15239)------------------------------
% 1.68/0.61  % (15253)Refutation not found, incomplete strategy% (15253)------------------------------
% 1.68/0.61  % (15253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.61  % (15253)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.61  
% 1.68/0.61  % (15253)Memory used [KB]: 6140
% 1.68/0.61  % (15253)Time elapsed: 0.194 s
% 1.68/0.61  % (15253)------------------------------
% 1.68/0.61  % (15253)------------------------------
% 1.68/0.61  % (15255)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.61  
% 1.68/0.61  % (15255)Memory used [KB]: 10618
% 1.68/0.61  % (15255)Time elapsed: 0.183 s
% 1.68/0.61  % (15255)------------------------------
% 1.68/0.61  % (15255)------------------------------
% 1.88/0.62  % (15249)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.88/0.63  % (15244)Refutation not found, incomplete strategy% (15244)------------------------------
% 1.88/0.63  % (15244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.63  % (15244)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.63  
% 1.88/0.63  % (15244)Memory used [KB]: 1663
% 1.88/0.63  % (15244)Time elapsed: 0.201 s
% 1.88/0.63  % (15244)------------------------------
% 1.88/0.63  % (15244)------------------------------
% 2.16/0.72  % (15298)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.16/0.72  % (15296)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.16/0.73  % (15296)Refutation not found, incomplete strategy% (15296)------------------------------
% 2.16/0.73  % (15296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.73  % (15296)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.73  
% 2.16/0.73  % (15296)Memory used [KB]: 10618
% 2.16/0.73  % (15296)Time elapsed: 0.067 s
% 2.16/0.73  % (15296)------------------------------
% 2.16/0.73  % (15296)------------------------------
% 2.52/0.74  % (15294)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.52/0.74  % (15298)Refutation not found, incomplete strategy% (15298)------------------------------
% 2.52/0.74  % (15298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.74  % (15298)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.74  
% 2.52/0.74  % (15298)Memory used [KB]: 1663
% 2.52/0.74  % (15298)Time elapsed: 0.099 s
% 2.52/0.74  % (15298)------------------------------
% 2.52/0.74  % (15298)------------------------------
% 2.52/0.74  % (15295)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.52/0.75  % (15295)Refutation not found, incomplete strategy% (15295)------------------------------
% 2.52/0.75  % (15295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.75  % (15295)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.75  
% 2.52/0.75  % (15295)Memory used [KB]: 6140
% 2.52/0.75  % (15295)Time elapsed: 0.123 s
% 2.52/0.75  % (15295)------------------------------
% 2.52/0.75  % (15295)------------------------------
% 2.52/0.75  % (15242)Refutation not found, incomplete strategy% (15242)------------------------------
% 2.52/0.75  % (15242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.75  % (15242)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.75  
% 2.52/0.75  % (15242)Memory used [KB]: 6140
% 2.52/0.75  % (15242)Time elapsed: 0.315 s
% 2.52/0.75  % (15242)------------------------------
% 2.52/0.75  % (15242)------------------------------
% 2.52/0.75  % (15293)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.52/0.75  % (15301)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.52/0.75  % (15304)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.52/0.75  % (15229)Refutation not found, incomplete strategy% (15229)------------------------------
% 2.52/0.75  % (15229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.75  % (15229)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.75  
% 2.52/0.75  % (15229)Memory used [KB]: 6140
% 2.52/0.75  % (15229)Time elapsed: 0.330 s
% 2.52/0.75  % (15229)------------------------------
% 2.52/0.75  % (15229)------------------------------
% 2.52/0.76  % (15300)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.52/0.76  % (15299)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.52/0.76  % (15230)Refutation not found, incomplete strategy% (15230)------------------------------
% 2.52/0.76  % (15230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.76  % (15302)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.52/0.76  % (15299)Refutation not found, incomplete strategy% (15299)------------------------------
% 2.52/0.76  % (15299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.76  % (15297)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.52/0.76  % (15297)Refutation not found, incomplete strategy% (15297)------------------------------
% 2.52/0.76  % (15297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.76  % (15297)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.76  
% 2.52/0.76  % (15297)Memory used [KB]: 10618
% 2.52/0.76  % (15297)Time elapsed: 0.142 s
% 2.52/0.76  % (15297)------------------------------
% 2.52/0.76  % (15297)------------------------------
% 2.52/0.77  % (15230)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.77  
% 2.52/0.77  % (15230)Memory used [KB]: 6140
% 2.52/0.77  % (15230)Time elapsed: 0.331 s
% 2.52/0.77  % (15230)------------------------------
% 2.52/0.77  % (15230)------------------------------
% 2.52/0.77  % (15305)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.52/0.77  % (15303)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.52/0.77  % (15304)Refutation not found, incomplete strategy% (15304)------------------------------
% 2.52/0.77  % (15304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.77  % (15299)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.77  % (15304)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.77  
% 2.52/0.77  % (15304)Memory used [KB]: 10618
% 2.52/0.77  % (15304)Time elapsed: 0.125 s
% 2.52/0.77  
% 2.52/0.77  % (15299)Memory used [KB]: 10618
% 2.52/0.77  % (15304)------------------------------
% 2.52/0.77  % (15304)------------------------------
% 2.52/0.77  % (15299)Time elapsed: 0.132 s
% 2.52/0.77  % (15299)------------------------------
% 2.52/0.77  % (15299)------------------------------
% 2.52/0.77  % (15302)Refutation not found, incomplete strategy% (15302)------------------------------
% 2.52/0.77  % (15302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.77  % (15302)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.77  
% 2.52/0.77  % (15302)Memory used [KB]: 10746
% 2.52/0.77  % (15302)Time elapsed: 0.132 s
% 2.52/0.77  % (15302)------------------------------
% 2.52/0.77  % (15302)------------------------------
% 3.10/0.84  % (15342)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.10/0.84  % (15334)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.42/0.87  % (15334)Refutation not found, incomplete strategy% (15334)------------------------------
% 3.42/0.87  % (15334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.87  % (15334)Termination reason: Refutation not found, incomplete strategy
% 3.42/0.87  
% 3.42/0.87  % (15334)Memory used [KB]: 10618
% 3.42/0.87  % (15334)Time elapsed: 0.114 s
% 3.42/0.87  % (15334)------------------------------
% 3.42/0.87  % (15334)------------------------------
% 3.42/0.87  % (15358)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.42/0.87  % (15355)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.42/0.87  % (15355)Refutation not found, incomplete strategy% (15355)------------------------------
% 3.42/0.87  % (15355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.87  % (15355)Termination reason: Refutation not found, incomplete strategy
% 3.42/0.87  
% 3.42/0.87  % (15355)Memory used [KB]: 1663
% 3.42/0.87  % (15355)Time elapsed: 0.092 s
% 3.42/0.87  % (15355)------------------------------
% 3.42/0.87  % (15355)------------------------------
% 3.42/0.88  % (15352)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.42/0.88  % (15350)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.42/0.89  % (15349)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 3.42/0.89  % (15353)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 3.75/0.91  % (15301)Refutation not found, incomplete strategy% (15301)------------------------------
% 3.75/0.91  % (15301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.91  % (15301)Termination reason: Refutation not found, incomplete strategy
% 3.75/0.91  
% 3.75/0.91  % (15301)Memory used [KB]: 6268
% 3.75/0.91  % (15301)Time elapsed: 0.278 s
% 3.75/0.91  % (15301)------------------------------
% 3.75/0.91  % (15301)------------------------------
% 3.75/0.92  % (15234)Refutation found. Thanks to Tanya!
% 3.75/0.92  % SZS status Theorem for theBenchmark
% 3.75/0.92  % SZS output start Proof for theBenchmark
% 3.75/0.92  fof(f5204,plain,(
% 3.75/0.92    $false),
% 3.75/0.92    inference(trivial_inequality_removal,[],[f5203])).
% 3.75/0.92  fof(f5203,plain,(
% 3.75/0.92    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.75/0.92    inference(superposition,[],[f43,f3668])).
% 3.75/0.92  fof(f3668,plain,(
% 3.75/0.92    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 3.75/0.92    inference(backward_demodulation,[],[f90,f3667])).
% 3.75/0.92  fof(f3667,plain,(
% 3.75/0.92    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f3648,f300])).
% 3.75/0.92  fof(f300,plain,(
% 3.75/0.92    ( ! [X17,X18] : (k6_relat_1(k3_xboole_0(X17,X18)) = k8_relat_1(X17,k6_relat_1(k3_xboole_0(X17,X18)))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f299,f45])).
% 3.75/0.92  fof(f45,plain,(
% 3.75/0.92    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 3.75/0.92    inference(cnf_transformation,[],[f20])).
% 3.75/0.92  fof(f20,axiom,(
% 3.75/0.92    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 3.75/0.92  fof(f299,plain,(
% 3.75/0.92    ( ! [X17,X18] : (k8_relat_1(X17,k6_relat_1(k3_xboole_0(X17,X18))) = k4_relat_1(k6_relat_1(k3_xboole_0(X17,X18)))) )),
% 3.75/0.92    inference(superposition,[],[f162,f141])).
% 3.75/0.92  fof(f141,plain,(
% 3.75/0.92    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(k3_xboole_0(X1,X2),k6_relat_1(X1))) )),
% 3.75/0.92    inference(resolution,[],[f107,f52])).
% 3.75/0.92  fof(f52,plain,(
% 3.75/0.92    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.75/0.92    inference(cnf_transformation,[],[f2])).
% 3.75/0.92  fof(f2,axiom,(
% 3.75/0.92    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.75/0.92  fof(f107,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f106,f90])).
% 3.75/0.92  fof(f106,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f104,f46])).
% 3.75/0.92  fof(f46,plain,(
% 3.75/0.92    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.75/0.92    inference(cnf_transformation,[],[f19])).
% 3.75/0.92  fof(f19,axiom,(
% 3.75/0.92    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.75/0.92  fof(f104,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 3.75/0.92    inference(resolution,[],[f62,f44])).
% 3.75/0.92  fof(f44,plain,(
% 3.75/0.92    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.75/0.92    inference(cnf_transformation,[],[f11])).
% 3.75/0.92  fof(f11,axiom,(
% 3.75/0.92    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 3.75/0.92  fof(f62,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 3.75/0.92    inference(cnf_transformation,[],[f35])).
% 3.75/0.92  fof(f35,plain,(
% 3.75/0.92    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.75/0.92    inference(flattening,[],[f34])).
% 3.75/0.92  fof(f34,plain,(
% 3.75/0.92    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.75/0.92    inference(ennf_transformation,[],[f22])).
% 3.75/0.92  fof(f22,axiom,(
% 3.75/0.92    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 3.75/0.92  fof(f162,plain,(
% 3.75/0.92    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f161,f90])).
% 3.75/0.92  fof(f161,plain,(
% 3.75/0.92    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f160,f90])).
% 3.75/0.92  fof(f160,plain,(
% 3.75/0.92    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f158,f45])).
% 3.75/0.92  fof(f158,plain,(
% 3.75/0.92    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0)))) )),
% 3.75/0.92    inference(resolution,[],[f112,f44])).
% 3.75/0.92  fof(f112,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f110,f45])).
% 3.75/0.92  fof(f110,plain,(
% 3.75/0.92    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.75/0.92    inference(resolution,[],[f49,f44])).
% 3.75/0.92  fof(f49,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.75/0.92    inference(cnf_transformation,[],[f27])).
% 3.75/0.92  fof(f27,plain,(
% 3.75/0.92    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.75/0.92    inference(ennf_transformation,[],[f18])).
% 3.75/0.92  fof(f18,axiom,(
% 3.75/0.92    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 3.75/0.92  fof(f3648,plain,(
% 3.75/0.92    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1)))) )),
% 3.75/0.92    inference(resolution,[],[f267,f1606])).
% 3.75/0.92  fof(f1606,plain,(
% 3.75/0.92    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0)) )),
% 3.75/0.92    inference(resolution,[],[f199,f92])).
% 3.75/0.92  fof(f92,plain,(
% 3.75/0.92    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X1))) )),
% 3.75/0.92    inference(backward_demodulation,[],[f80,f90])).
% 3.75/0.92  fof(f80,plain,(
% 3.75/0.92    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1))) )),
% 3.75/0.92    inference(resolution,[],[f61,f44])).
% 3.75/0.92  fof(f61,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)) )),
% 3.75/0.92    inference(cnf_transformation,[],[f33])).
% 3.75/0.92  fof(f33,plain,(
% 3.75/0.92    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.75/0.92    inference(ennf_transformation,[],[f21])).
% 3.75/0.92  fof(f21,axiom,(
% 3.75/0.92    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 3.75/0.92  fof(f199,plain,(
% 3.75/0.92    ( ! [X35,X33,X34] : (~r1_tarski(k8_relat_1(X33,k6_relat_1(X34)),k6_relat_1(X35)) | r1_tarski(k1_relat_1(k8_relat_1(X33,k6_relat_1(X34))),X35)) )),
% 3.75/0.92    inference(resolution,[],[f144,f97])).
% 3.75/0.92  fof(f97,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,k6_relat_1(X1)) | r1_tarski(k1_relat_1(X0),X1)) )),
% 3.75/0.92    inference(forward_demodulation,[],[f95,f46])).
% 3.75/0.92  fof(f95,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~r1_tarski(X0,k6_relat_1(X1)) | r1_tarski(k1_relat_1(X0),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 3.75/0.92    inference(resolution,[],[f50,f44])).
% 3.75/0.92  fof(f50,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 3.75/0.92    inference(cnf_transformation,[],[f29])).
% 3.75/0.92  fof(f29,plain,(
% 3.75/0.92    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.75/0.92    inference(flattening,[],[f28])).
% 3.75/0.92  fof(f28,plain,(
% 3.75/0.92    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.75/0.92    inference(ennf_transformation,[],[f17])).
% 3.75/0.92  fof(f17,axiom,(
% 3.75/0.92    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 3.75/0.92  fof(f144,plain,(
% 3.75/0.92    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 3.75/0.92    inference(superposition,[],[f73,f103])).
% 3.75/0.92  fof(f103,plain,(
% 3.75/0.92    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(X1,X0))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f101,f46])).
% 3.75/0.92  fof(f101,plain,(
% 3.75/0.92    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0))) )),
% 3.75/0.92    inference(resolution,[],[f59,f44])).
% 3.75/0.92  fof(f59,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) )),
% 3.75/0.92    inference(cnf_transformation,[],[f32])).
% 3.75/0.92  fof(f32,plain,(
% 3.75/0.92    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.75/0.92    inference(ennf_transformation,[],[f14])).
% 3.75/0.92  fof(f14,axiom,(
% 3.75/0.92    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).
% 3.75/0.92  fof(f73,plain,(
% 3.75/0.92    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) )),
% 3.75/0.92    inference(resolution,[],[f57,f44])).
% 3.75/0.92  fof(f57,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 3.75/0.92    inference(cnf_transformation,[],[f30])).
% 3.75/0.92  fof(f30,plain,(
% 3.75/0.92    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 3.75/0.92    inference(ennf_transformation,[],[f12])).
% 3.75/0.92  fof(f12,axiom,(
% 3.75/0.92    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 3.75/0.92  fof(f267,plain,(
% 3.75/0.92    ( ! [X28,X26,X27] : (~r1_tarski(k1_relat_1(k8_relat_1(X26,k6_relat_1(X27))),X28) | k8_relat_1(X26,k6_relat_1(X27)) = k8_relat_1(X26,k6_relat_1(k3_xboole_0(X28,X27)))) )),
% 3.75/0.92    inference(backward_demodulation,[],[f197,f266])).
% 3.75/0.92  fof(f266,plain,(
% 3.75/0.92    ( ! [X39,X41,X40] : (k5_relat_1(k6_relat_1(X41),k8_relat_1(X40,k6_relat_1(X39))) = k8_relat_1(X40,k6_relat_1(k3_xboole_0(X41,X39)))) )),
% 3.75/0.92    inference(backward_demodulation,[],[f207,f265])).
% 3.75/0.92  fof(f265,plain,(
% 3.75/0.92    ( ! [X2,X3,X1] : (k8_relat_1(X3,k6_relat_1(k3_xboole_0(X1,X2))) = k4_relat_1(k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X3))))) )),
% 3.75/0.92    inference(superposition,[],[f162,f108])).
% 3.75/0.92  fof(f108,plain,(
% 3.75/0.92    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(k3_xboole_0(X0,X1),k6_relat_1(X2))) )),
% 3.75/0.92    inference(resolution,[],[f67,f44])).
% 3.75/0.92  fof(f67,plain,(
% 3.75/0.92    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 3.75/0.92    inference(cnf_transformation,[],[f36])).
% 3.75/0.92  fof(f36,plain,(
% 3.75/0.92    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.75/0.92    inference(ennf_transformation,[],[f16])).
% 3.75/0.92  fof(f16,axiom,(
% 3.75/0.92    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).
% 3.75/0.92  fof(f207,plain,(
% 3.75/0.92    ( ! [X39,X41,X40] : (k5_relat_1(k6_relat_1(X41),k8_relat_1(X40,k6_relat_1(X39))) = k4_relat_1(k8_relat_1(X41,k8_relat_1(X39,k6_relat_1(X40))))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f206,f193])).
% 3.75/0.92  fof(f193,plain,(
% 3.75/0.92    ( ! [X14,X15,X16] : (k8_relat_1(X14,k8_relat_1(X15,k6_relat_1(X16))) = k5_relat_1(k8_relat_1(X15,k6_relat_1(X16)),k6_relat_1(X14))) )),
% 3.75/0.92    inference(resolution,[],[f144,f58])).
% 3.75/0.92  fof(f58,plain,(
% 3.75/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 3.75/0.92    inference(cnf_transformation,[],[f31])).
% 3.75/0.92  fof(f31,plain,(
% 3.75/0.92    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 3.75/0.92    inference(ennf_transformation,[],[f13])).
% 3.75/0.92  fof(f13,axiom,(
% 3.75/0.92    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 3.75/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 3.75/0.92  fof(f206,plain,(
% 3.75/0.92    ( ! [X39,X41,X40] : (k4_relat_1(k5_relat_1(k8_relat_1(X39,k6_relat_1(X40)),k6_relat_1(X41))) = k5_relat_1(k6_relat_1(X41),k8_relat_1(X40,k6_relat_1(X39)))) )),
% 3.75/0.92    inference(forward_demodulation,[],[f201,f162])).
% 3.75/0.92  fof(f201,plain,(
% 3.75/0.92    ( ! [X39,X41,X40] : (k4_relat_1(k5_relat_1(k8_relat_1(X39,k6_relat_1(X40)),k6_relat_1(X41))) = k5_relat_1(k6_relat_1(X41),k4_relat_1(k8_relat_1(X39,k6_relat_1(X40))))) )),
% 3.75/0.92    inference(resolution,[],[f144,f112])).
% 3.75/0.93  fof(f197,plain,(
% 3.75/0.93    ( ! [X28,X26,X27] : (~r1_tarski(k1_relat_1(k8_relat_1(X26,k6_relat_1(X27))),X28) | k8_relat_1(X26,k6_relat_1(X27)) = k5_relat_1(k6_relat_1(X28),k8_relat_1(X26,k6_relat_1(X27)))) )),
% 3.75/0.93    inference(resolution,[],[f144,f62])).
% 3.75/0.93  fof(f90,plain,(
% 3.75/0.93    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 3.75/0.93    inference(resolution,[],[f58,f44])).
% 3.75/0.93  fof(f43,plain,(
% 3.75/0.93    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.75/0.93    inference(cnf_transformation,[],[f40])).
% 3.75/0.93  fof(f40,plain,(
% 3.75/0.93    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.75/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f39])).
% 3.75/0.93  fof(f39,plain,(
% 3.75/0.93    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.75/0.93    introduced(choice_axiom,[])).
% 3.75/0.93  fof(f25,plain,(
% 3.75/0.93    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.75/0.93    inference(ennf_transformation,[],[f24])).
% 3.75/0.93  fof(f24,negated_conjecture,(
% 3.75/0.93    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.75/0.93    inference(negated_conjecture,[],[f23])).
% 3.75/0.93  fof(f23,conjecture,(
% 3.75/0.93    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.75/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 3.75/0.93  % SZS output end Proof for theBenchmark
% 3.75/0.93  % (15234)------------------------------
% 3.75/0.93  % (15234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.93  % (15234)Termination reason: Refutation
% 3.75/0.93  
% 3.75/0.93  % (15234)Memory used [KB]: 5756
% 3.75/0.93  % (15234)Time elapsed: 0.441 s
% 3.75/0.93  % (15234)------------------------------
% 3.75/0.93  % (15234)------------------------------
% 3.75/0.93  % (15226)Success in time 0.574 s
%------------------------------------------------------------------------------
