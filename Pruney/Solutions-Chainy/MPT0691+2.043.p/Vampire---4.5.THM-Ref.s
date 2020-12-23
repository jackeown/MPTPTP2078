%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 196 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :   21
%              Number of atoms          :  167 ( 437 expanded)
%              Number of equality atoms :   70 (  89 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21867)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f393,plain,(
    $false ),
    inference(resolution,[],[f392,f40])).

fof(f40,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f392,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f391,f153])).

fof(f153,plain,(
    sK0 = k5_xboole_0(k1_relat_1(sK1),k5_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f152,f51])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f152,plain,(
    sK0 = k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f151,f105])).

fof(f105,plain,(
    k1_relat_1(sK1) = k5_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f66,f39])).

fof(f39,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(definition_unfolding,[],[f60,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f151,plain,(
    sK0 = k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK1)),k5_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(resolution,[],[f65,f39])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = X0 ) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f53,f52])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f391,plain,(
    r1_tarski(k5_xboole_0(k1_relat_1(sK1),k5_xboole_0(sK0,k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f390,f51])).

fof(f390,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(sK1)),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f389,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f389,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK1)),k5_xboole_0(k1_relat_1(sK1),k1_xboole_0)),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f388,f51])).

fof(f388,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(sK1),k1_xboole_0),k5_xboole_0(sK0,k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f387,f51])).

fof(f387,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(sK1),k1_xboole_0),k5_xboole_0(k1_relat_1(sK1),sK0)),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f384,f51])).

fof(f384,plain,(
    r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(sK1),sK0),k5_xboole_0(k1_relat_1(sK1),k1_xboole_0)),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f203,f88])).

fof(f88,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f62,f39])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f203,plain,(
    ! [X7] : r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(sK1),X7),k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(X7,k1_relat_1(sK1)))),k10_relat_1(sK1,k9_relat_1(sK1,X7))) ),
    inference(backward_demodulation,[],[f167,f202])).

fof(f202,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k9_relat_1(k4_relat_1(sK1),X7) ),
    inference(forward_demodulation,[],[f199,f192])).

fof(f192,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) ),
    inference(backward_demodulation,[],[f179,f191])).

fof(f191,plain,(
    ! [X1] : k4_relat_1(k8_relat_1(X1,sK1)) = k7_relat_1(k4_relat_1(sK1),X1) ),
    inference(backward_demodulation,[],[f142,f188])).

fof(f188,plain,(
    ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1)) ),
    inference(resolution,[],[f95,f38])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f142,plain,(
    ! [X1] : k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X1,sK1)) ),
    inference(forward_demodulation,[],[f141,f94])).

fof(f94,plain,(
    ! [X7] : k8_relat_1(X7,sK1) = k5_relat_1(sK1,k6_relat_1(X7)) ),
    inference(resolution,[],[f55,f38])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f141,plain,(
    ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f138,f43])).

fof(f43,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f138,plain,(
    ! [X1] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(sK1)) ),
    inference(resolution,[],[f135,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f135,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)) ) ),
    inference(resolution,[],[f50,f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f179,plain,(
    ! [X7] : k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1))) = k10_relat_1(sK1,X7) ),
    inference(forward_demodulation,[],[f178,f131])).

fof(f131,plain,(
    ! [X1] : k10_relat_1(sK1,X1) = k1_relat_1(k8_relat_1(X1,sK1)) ),
    inference(forward_demodulation,[],[f130,f94])).

fof(f130,plain,(
    ! [X1] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k10_relat_1(sK1,X1) ),
    inference(forward_demodulation,[],[f127,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f127,plain,(
    ! [X1] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X1))) ),
    inference(resolution,[],[f125,f41])).

fof(f125,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k1_relat_1(k5_relat_1(sK1,X7)) = k10_relat_1(sK1,k1_relat_1(X7)) ) ),
    inference(resolution,[],[f49,f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f178,plain,(
    ! [X7] : k1_relat_1(k8_relat_1(X7,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1))) ),
    inference(resolution,[],[f84,f38])).

fof(f84,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k8_relat_1(X2,X3)) = k2_relat_1(k4_relat_1(k8_relat_1(X2,X3))) ) ),
    inference(resolution,[],[f48,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f199,plain,(
    ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7) ),
    inference(resolution,[],[f100,f38])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1) ) ),
    inference(resolution,[],[f57,f46])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f167,plain,(
    ! [X7] : r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(sK1),X7),k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(X7,k1_relat_1(sK1)))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X7))) ),
    inference(resolution,[],[f64,f38])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(X1),X0),k5_xboole_0(k1_relat_1(X1),k4_xboole_0(X0,k1_relat_1(X1)))),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    inference(definition_unfolding,[],[f58,f63])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (21858)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.45  % (21870)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (21860)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (21857)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (21872)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (21862)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (21865)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (21869)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (21871)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (21856)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (21866)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (21855)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (21861)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (21864)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (21859)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (21856)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (21868)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (21863)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  % (21867)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  fof(f393,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(resolution,[],[f392,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f20])).
% 0.21/0.50  fof(f20,conjecture,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.50  fof(f392,plain,(
% 0.21/0.50    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f391,f153])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    sK0 = k5_xboole_0(k1_relat_1(sK1),k5_xboole_0(sK0,k1_relat_1(sK1)))),
% 0.21/0.50    inference(superposition,[],[f152,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    sK0 = k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(sK1))),
% 0.21/0.50    inference(forward_demodulation,[],[f151,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    k1_relat_1(sK1) = k5_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK1),sK0))),
% 0.21/0.50    inference(resolution,[],[f66,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.21/0.50    inference(definition_unfolding,[],[f60,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    sK0 = k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK1)),k5_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK1),sK0)))),
% 0.21/0.50    inference(resolution,[],[f65,f39])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f59,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f53,f52])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    r1_tarski(k5_xboole_0(k1_relat_1(sK1),k5_xboole_0(sK0,k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f390,f51])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    r1_tarski(k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(sK1)),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f389,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.50  fof(f389,plain,(
% 0.21/0.50    r1_tarski(k5_xboole_0(k5_xboole_0(sK0,k1_relat_1(sK1)),k5_xboole_0(k1_relat_1(sK1),k1_xboole_0)),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f388,f51])).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(sK1),k1_xboole_0),k5_xboole_0(sK0,k1_relat_1(sK1))),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f387,f51])).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(sK1),k1_xboole_0),k5_xboole_0(k1_relat_1(sK1),sK0)),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f384,f51])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(sK1),sK0),k5_xboole_0(k1_relat_1(sK1),k1_xboole_0)),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.50    inference(superposition,[],[f203,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k1_relat_1(sK1))),
% 0.21/0.50    inference(resolution,[],[f62,f39])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ( ! [X7] : (r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(sK1),X7),k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(X7,k1_relat_1(sK1)))),k10_relat_1(sK1,k9_relat_1(sK1,X7)))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f167,f202])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    ( ! [X7] : (k10_relat_1(sK1,X7) = k9_relat_1(k4_relat_1(sK1),X7)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f199,f192])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    ( ! [X7] : (k10_relat_1(sK1,X7) = k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f179,f191])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X1] : (k4_relat_1(k8_relat_1(X1,sK1)) = k7_relat_1(k4_relat_1(sK1),X1)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f142,f188])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ( ! [X7] : (k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))) )),
% 0.21/0.50    inference(resolution,[],[f95,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f56,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ( ! [X1] : (k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X1,sK1))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f141,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X7] : (k8_relat_1(X7,sK1) = k5_relat_1(sK1,k6_relat_1(X7))) )),
% 0.21/0.50    inference(resolution,[],[f55,f38])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f138,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,axiom,(
% 0.21/0.50    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ( ! [X1] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(sK1))) )),
% 0.21/0.50    inference(resolution,[],[f135,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1))) )),
% 0.21/0.50    inference(resolution,[],[f50,f38])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    ( ! [X7] : (k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1))) = k10_relat_1(sK1,X7)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f178,f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X1] : (k10_relat_1(sK1,X1) = k1_relat_1(k8_relat_1(X1,sK1))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f130,f94])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ( ! [X1] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k10_relat_1(sK1,X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f127,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X1] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X1))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X1)))) )),
% 0.21/0.50    inference(resolution,[],[f125,f41])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X7] : (~v1_relat_1(X7) | k1_relat_1(k5_relat_1(sK1,X7)) = k10_relat_1(sK1,k1_relat_1(X7))) )),
% 0.21/0.50    inference(resolution,[],[f49,f38])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    ( ! [X7] : (k1_relat_1(k8_relat_1(X7,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1)))) )),
% 0.21/0.50    inference(resolution,[],[f84,f38])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~v1_relat_1(X3) | k1_relat_1(k8_relat_1(X2,X3)) = k2_relat_1(k4_relat_1(k8_relat_1(X2,X3)))) )),
% 0.21/0.50    inference(resolution,[],[f48,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ( ! [X7] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)) )),
% 0.21/0.50    inference(resolution,[],[f100,f38])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)) )),
% 0.21/0.50    inference(resolution,[],[f57,f46])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X7] : (r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(sK1),X7),k5_xboole_0(k1_relat_1(sK1),k4_xboole_0(X7,k1_relat_1(sK1)))),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X7)))) )),
% 0.21/0.50    inference(resolution,[],[f64,f38])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_xboole_0(k5_xboole_0(k1_relat_1(X1),X0),k5_xboole_0(k1_relat_1(X1),k4_xboole_0(X0,k1_relat_1(X1)))),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f58,f63])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (21856)------------------------------
% 0.21/0.50  % (21856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21856)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (21856)Memory used [KB]: 1918
% 0.21/0.50  % (21856)Time elapsed: 0.081 s
% 0.21/0.50  % (21856)------------------------------
% 0.21/0.50  % (21856)------------------------------
% 0.21/0.50  % (21854)Success in time 0.146 s
%------------------------------------------------------------------------------
