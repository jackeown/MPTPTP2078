%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 172 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 338 expanded)
%              Number of equality atoms :   62 (  87 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(global_subsumption,[],[f34,f352])).

fof(f352,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f216,f341])).

fof(f341,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k9_relat_1(k4_relat_1(sK1),X7) ),
    inference(forward_demodulation,[],[f340,f263])).

fof(f263,plain,(
    ! [X7] : k10_relat_1(sK1,X7) = k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1))) ),
    inference(forward_demodulation,[],[f261,f153])).

fof(f153,plain,(
    ! [X3] : k10_relat_1(sK1,X3) = k1_relat_1(k8_relat_1(X3,sK1)) ),
    inference(forward_demodulation,[],[f152,f67])).

fof(f67,plain,(
    ! [X7] : k8_relat_1(X7,sK1) = k5_relat_1(sK1,k6_relat_1(X7)) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f152,plain,(
    ! [X3] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3))) = k10_relat_1(sK1,X3) ),
    inference(forward_demodulation,[],[f150,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f150,plain,(
    ! [X3] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X3))) ),
    inference(resolution,[],[f101,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f101,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k1_relat_1(k5_relat_1(sK1,X7)) = k10_relat_1(sK1,k1_relat_1(X7)) ) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f261,plain,(
    ! [X7] : k1_relat_1(k8_relat_1(X7,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1))) ),
    inference(resolution,[],[f59,f32])).

fof(f59,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(k8_relat_1(X1,X2)) = k2_relat_1(k4_relat_1(k8_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f41,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f340,plain,(
    ! [X7] : k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1))) = k9_relat_1(k4_relat_1(sK1),X7) ),
    inference(forward_demodulation,[],[f285,f276])).

fof(f276,plain,(
    ! [X7] : k4_relat_1(k8_relat_1(X7,sK1)) = k7_relat_1(k4_relat_1(sK1),X7) ),
    inference(forward_demodulation,[],[f273,f167])).

fof(f167,plain,(
    ! [X3] : k5_relat_1(k6_relat_1(X3),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X3,sK1)) ),
    inference(forward_demodulation,[],[f166,f67])).

fof(f166,plain,(
    ! [X3] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X3))) = k5_relat_1(k6_relat_1(X3),k4_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f164,f35])).

fof(f35,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f164,plain,(
    ! [X3] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X3))) = k5_relat_1(k4_relat_1(k6_relat_1(X3)),k4_relat_1(sK1)) ),
    inference(resolution,[],[f139,f36])).

fof(f139,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1)) ) ),
    inference(resolution,[],[f43,f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f273,plain,(
    ! [X7] : k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1)) ),
    inference(resolution,[],[f68,f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(resolution,[],[f46,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f285,plain,(
    ! [X7] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7) ),
    inference(resolution,[],[f72,f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1) ) ),
    inference(resolution,[],[f47,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f216,plain,(
    r1_tarski(sK0,k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(global_subsumption,[],[f32,f215])).

fof(f215,plain,
    ( r1_tarski(sK0,k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f49,f211])).

fof(f211,plain,(
    sK0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f210,f33])).

fof(f33,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(forward_demodulation,[],[f209,f205])).

fof(f205,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k1_relat_1(k8_relat_1(X5,k6_relat_1(X6))) ),
    inference(backward_demodulation,[],[f80,f202])).

fof(f202,plain,(
    ! [X6,X5] : k8_relat_1(X5,k6_relat_1(X6)) = k7_relat_1(k6_relat_1(X5),X6) ),
    inference(forward_demodulation,[],[f70,f66])).

fof(f66,plain,(
    ! [X6,X5] : k8_relat_1(X5,k6_relat_1(X6)) = k5_relat_1(k6_relat_1(X6),k6_relat_1(X5)) ),
    inference(resolution,[],[f45,f36])).

fof(f70,plain,(
    ! [X6,X5] : k5_relat_1(k6_relat_1(X6),k6_relat_1(X5)) = k7_relat_1(k6_relat_1(X5),X6) ),
    inference(resolution,[],[f46,f36])).

fof(f80,plain,(
    ! [X6,X5] : k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k3_xboole_0(X5,X6) ),
    inference(forward_demodulation,[],[f78,f37])).

fof(f78,plain,(
    ! [X6,X5] : k3_xboole_0(k1_relat_1(k6_relat_1(X5)),X6) = k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) ),
    inference(resolution,[],[f48,f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f209,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(forward_demodulation,[],[f85,f202])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = X1 ) ),
    inference(global_subsumption,[],[f36,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = X1 ) ),
    inference(superposition,[],[f50,f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).

fof(f34,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (16001)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.46  % (16009)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.48  % (16001)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f356,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(global_subsumption,[],[f34,f352])).
% 0.20/0.48  fof(f352,plain,(
% 0.20/0.48    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.20/0.48    inference(backward_demodulation,[],[f216,f341])).
% 0.20/0.48  fof(f341,plain,(
% 0.20/0.48    ( ! [X7] : (k10_relat_1(sK1,X7) = k9_relat_1(k4_relat_1(sK1),X7)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f340,f263])).
% 0.20/0.48  fof(f263,plain,(
% 0.20/0.48    ( ! [X7] : (k10_relat_1(sK1,X7) = k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1)))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f261,f153])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    ( ! [X3] : (k10_relat_1(sK1,X3) = k1_relat_1(k8_relat_1(X3,sK1))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f152,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X7] : (k8_relat_1(X7,sK1) = k5_relat_1(sK1,k6_relat_1(X7))) )),
% 0.20/0.48    inference(resolution,[],[f45,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f15])).
% 0.20/0.48  fof(f15,conjecture,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    ( ! [X3] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3))) = k10_relat_1(sK1,X3)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f150,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    ( ! [X3] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X3))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X3)))) )),
% 0.20/0.48    inference(resolution,[],[f101,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ( ! [X7] : (~v1_relat_1(X7) | k1_relat_1(k5_relat_1(sK1,X7)) = k10_relat_1(sK1,k1_relat_1(X7))) )),
% 0.20/0.48    inference(resolution,[],[f42,f32])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.48  fof(f261,plain,(
% 0.20/0.48    ( ! [X7] : (k1_relat_1(k8_relat_1(X7,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1)))) )),
% 0.20/0.48    inference(resolution,[],[f59,f32])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v1_relat_1(X2) | k1_relat_1(k8_relat_1(X1,X2)) = k2_relat_1(k4_relat_1(k8_relat_1(X1,X2)))) )),
% 0.20/0.48    inference(resolution,[],[f41,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.48  fof(f340,plain,(
% 0.20/0.48    ( ! [X7] : (k2_relat_1(k4_relat_1(k8_relat_1(X7,sK1))) = k9_relat_1(k4_relat_1(sK1),X7)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f285,f276])).
% 0.20/0.48  fof(f276,plain,(
% 0.20/0.48    ( ! [X7] : (k4_relat_1(k8_relat_1(X7,sK1)) = k7_relat_1(k4_relat_1(sK1),X7)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f273,f167])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    ( ! [X3] : (k5_relat_1(k6_relat_1(X3),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X3,sK1))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f166,f67])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    ( ! [X3] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X3))) = k5_relat_1(k6_relat_1(X3),k4_relat_1(sK1))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f164,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.20/0.48  fof(f164,plain,(
% 0.20/0.48    ( ! [X3] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X3))) = k5_relat_1(k4_relat_1(k6_relat_1(X3)),k4_relat_1(sK1))) )),
% 0.20/0.48    inference(resolution,[],[f139,f36])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(sK1,X7)) = k5_relat_1(k4_relat_1(X7),k4_relat_1(sK1))) )),
% 0.20/0.48    inference(resolution,[],[f43,f32])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.20/0.48  fof(f273,plain,(
% 0.20/0.48    ( ! [X7] : (k7_relat_1(k4_relat_1(sK1),X7) = k5_relat_1(k6_relat_1(X7),k4_relat_1(sK1))) )),
% 0.20/0.48    inference(resolution,[],[f68,f32])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k4_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) )),
% 0.20/0.48    inference(resolution,[],[f46,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    ( ! [X7] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X7)) = k9_relat_1(k4_relat_1(sK1),X7)) )),
% 0.20/0.48    inference(resolution,[],[f72,f32])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)) )),
% 0.20/0.48    inference(resolution,[],[f47,f39])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    r1_tarski(sK0,k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 0.20/0.48    inference(global_subsumption,[],[f32,f215])).
% 0.20/0.48  fof(f215,plain,(
% 0.20/0.48    r1_tarski(sK0,k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) | ~v1_relat_1(sK1)),
% 0.20/0.48    inference(superposition,[],[f49,f211])).
% 0.20/0.48  fof(f211,plain,(
% 0.20/0.48    sK0 = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.48    inference(resolution,[],[f210,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_xboole_0(X0,X1) = X1) )),
% 0.20/0.48    inference(forward_demodulation,[],[f209,f205])).
% 0.20/0.48  fof(f205,plain,(
% 0.20/0.48    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k1_relat_1(k8_relat_1(X5,k6_relat_1(X6)))) )),
% 0.20/0.48    inference(backward_demodulation,[],[f80,f202])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    ( ! [X6,X5] : (k8_relat_1(X5,k6_relat_1(X6)) = k7_relat_1(k6_relat_1(X5),X6)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f70,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X6,X5] : (k8_relat_1(X5,k6_relat_1(X6)) = k5_relat_1(k6_relat_1(X6),k6_relat_1(X5))) )),
% 0.20/0.48    inference(resolution,[],[f45,f36])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X6,X5] : (k5_relat_1(k6_relat_1(X6),k6_relat_1(X5)) = k7_relat_1(k6_relat_1(X5),X6)) )),
% 0.20/0.48    inference(resolution,[],[f46,f36])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X6,X5] : (k1_relat_1(k7_relat_1(k6_relat_1(X5),X6)) = k3_xboole_0(X5,X6)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f78,f37])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X6,X5] : (k3_xboole_0(k1_relat_1(k6_relat_1(X5)),X6) = k1_relat_1(k7_relat_1(k6_relat_1(X5),X6))) )),
% 0.20/0.48    inference(resolution,[],[f48,f36])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = X1 | ~r1_tarski(X1,X0)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f85,f202])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = X1) )),
% 0.20/0.48    inference(global_subsumption,[],[f36,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = X1) )),
% 0.20/0.48    inference(superposition,[],[f50,f37])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (16001)------------------------------
% 0.20/0.48  % (16001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (16001)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.49  % (16001)Memory used [KB]: 11001
% 0.20/0.49  % (16001)Time elapsed: 0.074 s
% 0.20/0.49  % (16001)------------------------------
% 0.20/0.49  % (16001)------------------------------
% 0.20/0.49  % (15998)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.49  % (15994)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (15988)Success in time 0.133 s
%------------------------------------------------------------------------------
