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
% DateTime   : Thu Dec  3 12:52:34 EST 2020

% Result     : Theorem 2.15s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  134 (14158 expanded)
%              Number of leaves         :   19 (4117 expanded)
%              Depth                    :   32
%              Number of atoms          :  199 (20927 expanded)
%              Number of equality atoms :  118 (10069 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3930,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f81,f91,f3383,f3849,f3863])).

fof(f3863,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f3862])).

fof(f3862,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f3713,f83])).

fof(f83,plain,(
    ! [X4,X3] : k8_relat_1(X4,k6_relat_1(X3)) = k7_relat_1(k6_relat_1(X4),X3) ),
    inference(superposition,[],[f72,f70])).

fof(f70,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f72,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f3713,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_2 ),
    inference(superposition,[],[f80,f3064])).

fof(f3064,plain,(
    ! [X10,X9] : k7_relat_1(k6_relat_1(X10),X9) = k6_relat_1(k3_xboole_0(X10,X9)) ),
    inference(superposition,[],[f2692,f1148])).

fof(f1148,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f1136,f246])).

fof(f246,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f236,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f236,plain,(
    ! [X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X0) = k1_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f98,f231])).

fof(f231,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(k3_xboole_0(X1,X2)),X1) ),
    inference(forward_demodulation,[],[f230,f40])).

fof(f40,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f230,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(k3_xboole_0(X1,X2)),X1) = k4_relat_1(k6_relat_1(k3_xboole_0(X1,X2))) ),
    inference(superposition,[],[f222,f138])).

fof(f138,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f136,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f135,f83])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f134,f70])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f131,f42])).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f56,f39])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f222,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f221,f83])).

fof(f221,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f220,f70])).

fof(f220,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f219,f83])).

fof(f219,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f218,f70])).

fof(f218,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f215,f40])).

fof(f215,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f214,f39])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f211,f40])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f46,f39])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f98,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f96,f41])).

fof(f96,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(resolution,[],[f54,f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f1136,plain,(
    ! [X6,X7] : k3_xboole_0(k3_xboole_0(X6,X7),X6) = k3_xboole_0(X7,X6) ),
    inference(forward_demodulation,[],[f1135,f699])).

fof(f699,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(k3_xboole_0(X4,X5),X5) ),
    inference(forward_demodulation,[],[f697,f98])).

fof(f697,plain,(
    ! [X4,X5] : k3_xboole_0(k3_xboole_0(X4,X5),X5) = k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) ),
    inference(superposition,[],[f127,f675])).

fof(f675,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(forward_demodulation,[],[f674,f83])).

fof(f674,plain,(
    ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(forward_demodulation,[],[f665,f70])).

fof(f665,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(superposition,[],[f663,f66])).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f64,f41])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f663,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(forward_demodulation,[],[f662,f83])).

fof(f662,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k8_relat_1(X2,k6_relat_1(X0)),X1) ),
    inference(forward_demodulation,[],[f659,f70])).

fof(f659,plain,(
    ! [X2,X0,X1] : k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X2)),X1) ),
    inference(resolution,[],[f226,f39])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) = k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) ) ),
    inference(resolution,[],[f57,f39])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f127,plain,(
    ! [X14,X15,X13] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X13),X14),X15)) = k3_xboole_0(k3_xboole_0(X13,X14),X15) ),
    inference(forward_demodulation,[],[f122,f98])).

fof(f122,plain,(
    ! [X14,X15,X13] : k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X13),X14),X15)) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(X13),X14)),X15) ),
    inference(resolution,[],[f116,f54])).

fof(f116,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(subsumption_resolution,[],[f114,f39])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f51,f113])).

fof(f113,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(X1,X0)) ),
    inference(forward_demodulation,[],[f112,f83])).

fof(f112,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(X1,X0)) ),
    inference(forward_demodulation,[],[f110,f41])).

fof(f110,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0)) ),
    inference(resolution,[],[f55,f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1135,plain,(
    ! [X6,X7] : k3_xboole_0(k3_xboole_0(k3_xboole_0(X6,X7),X7),X6) = k3_xboole_0(X7,X6) ),
    inference(forward_demodulation,[],[f1125,f98])).

fof(f1125,plain,(
    ! [X6,X7] : k3_xboole_0(k3_xboole_0(k3_xboole_0(X6,X7),X7),X6) = k1_relat_1(k7_relat_1(k6_relat_1(X7),X6)) ),
    inference(superposition,[],[f127,f771])).

fof(f771,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X1),X0) ),
    inference(superposition,[],[f672,f470])).

fof(f470,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k8_relat_1(k3_xboole_0(X0,X1),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f462,f222])).

fof(f462,plain,(
    ! [X0,X1] : k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k8_relat_1(k3_xboole_0(X0,X1),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[],[f225,f126])).

fof(f126,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f117,f98])).

fof(f117,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(resolution,[],[f116,f43])).

fof(f225,plain,(
    ! [X6,X7,X5] : k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) ),
    inference(forward_demodulation,[],[f224,f121])).

fof(f121,plain,(
    ! [X12,X10,X11] : k7_relat_1(k7_relat_1(k6_relat_1(X10),X11),X12) = k5_relat_1(k6_relat_1(X12),k7_relat_1(k6_relat_1(X10),X11)) ),
    inference(resolution,[],[f116,f53])).

fof(f224,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6)) ),
    inference(forward_demodulation,[],[f223,f120])).

fof(f120,plain,(
    ! [X8,X7,X9] : k8_relat_1(X7,k7_relat_1(k6_relat_1(X8),X9)) = k5_relat_1(k7_relat_1(k6_relat_1(X8),X9),k6_relat_1(X7)) ),
    inference(resolution,[],[f116,f52])).

fof(f223,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5)) ),
    inference(forward_demodulation,[],[f217,f222])).

fof(f217,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5)) ),
    inference(resolution,[],[f214,f116])).

fof(f672,plain,(
    ! [X4,X5,X3] : k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4) ),
    inference(superposition,[],[f663,f120])).

fof(f2692,plain,(
    ! [X23,X22] : k7_relat_1(k6_relat_1(X22),X23) = k6_relat_1(k3_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f2691,f1336])).

fof(f1336,plain,(
    ! [X41,X40] : k7_relat_1(k6_relat_1(X41),X40) = k7_relat_1(k6_relat_1(k3_xboole_0(X41,X40)),X40) ),
    inference(forward_demodulation,[],[f1244,f231])).

fof(f1244,plain,(
    ! [X41,X40] : k7_relat_1(k6_relat_1(X41),X40) = k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(X41,X40)),X41),X40) ),
    inference(superposition,[],[f771,f1148])).

fof(f2691,plain,(
    ! [X23,X22] : k6_relat_1(k3_xboole_0(X23,X22)) = k7_relat_1(k6_relat_1(k3_xboole_0(X22,X23)),X23) ),
    inference(forward_demodulation,[],[f2614,f1197])).

fof(f1197,plain,(
    ! [X50,X49] : k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(X50,X49)),X49),k3_xboole_0(X49,X50)) = k6_relat_1(k3_xboole_0(X49,X50)) ),
    inference(forward_demodulation,[],[f1173,f138])).

fof(f1173,plain,(
    ! [X50,X49] : k7_relat_1(k6_relat_1(X49),k3_xboole_0(X49,X50)) = k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(X50,X49)),X49),k3_xboole_0(X49,X50)) ),
    inference(superposition,[],[f771,f1136])).

fof(f2614,plain,(
    ! [X23,X22] : k7_relat_1(k6_relat_1(k3_xboole_0(X22,X23)),X23) = k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(X22,X23)),X23),k3_xboole_0(X23,X22)) ),
    inference(superposition,[],[f126,f2317])).

fof(f2317,plain,(
    ! [X87,X86] : k3_xboole_0(X86,X87) = k3_xboole_0(k3_xboole_0(X87,X86),X86) ),
    inference(forward_demodulation,[],[f2316,f149])).

fof(f149,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f147,f41])).

fof(f147,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k3_xboole_0(X6,X7)) = k1_relat_1(k6_relat_1(k3_xboole_0(X6,X7))) ),
    inference(superposition,[],[f98,f138])).

fof(f2316,plain,(
    ! [X87,X86] : k3_xboole_0(k3_xboole_0(X87,X86),X86) = k3_xboole_0(X86,k3_xboole_0(X86,X87)) ),
    inference(forward_demodulation,[],[f2262,f1148])).

fof(f2262,plain,(
    ! [X87,X86] : k3_xboole_0(k3_xboole_0(X87,X86),X86) = k3_xboole_0(k3_xboole_0(X86,X87),X86) ),
    inference(superposition,[],[f1136,f1212])).

fof(f1212,plain,(
    ! [X8,X7] : k3_xboole_0(X8,X7) = k3_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f1148,f1136])).

fof(f80,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_2
  <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k8_relat_1(sK0,k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f3849,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f3848])).

fof(f3848,plain,
    ( $false
    | spl2_3 ),
    inference(trivial_inequality_removal,[],[f3712])).

fof(f3712,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_3 ),
    inference(superposition,[],[f90,f3064])).

fof(f90,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_3
  <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f3383,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f3110,f88,f3380])).

fof(f3380,plain,
    ( spl2_4
  <=> k7_relat_1(k6_relat_1(sK0),sK1) = k7_relat_1(k6_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f3110,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0)
    | spl2_3 ),
    inference(superposition,[],[f90,f2692])).

fof(f91,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f84,f60,f88])).

fof(f60,plain,
    ( spl2_1
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f84,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(superposition,[],[f62,f72])).

fof(f62,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f81,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f75,f60,f78])).

fof(f75,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_1 ),
    inference(superposition,[],[f62,f70])).

fof(f63,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f38,f60])).

fof(f38,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f36])).

fof(f36,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:15:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (5112)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (5120)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (5113)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (5121)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (5111)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (5117)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (5127)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (5115)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (5124)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (5118)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (5114)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (5122)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (5119)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (5122)Refutation not found, incomplete strategy% (5122)------------------------------
% 0.22/0.50  % (5122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5122)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (5122)Memory used [KB]: 10618
% 0.22/0.50  % (5122)Time elapsed: 0.085 s
% 0.22/0.50  % (5122)------------------------------
% 0.22/0.50  % (5122)------------------------------
% 0.22/0.51  % (5116)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (5128)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (5126)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (5125)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.53  % (5123)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 2.15/0.70  % (5111)Refutation found. Thanks to Tanya!
% 2.15/0.70  % SZS status Theorem for theBenchmark
% 2.15/0.70  % SZS output start Proof for theBenchmark
% 2.15/0.70  fof(f3930,plain,(
% 2.15/0.70    $false),
% 2.15/0.70    inference(avatar_sat_refutation,[],[f63,f81,f91,f3383,f3849,f3863])).
% 2.15/0.70  fof(f3863,plain,(
% 2.15/0.70    spl2_2),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f3862])).
% 2.15/0.70  fof(f3862,plain,(
% 2.15/0.70    $false | spl2_2),
% 2.15/0.70    inference(subsumption_resolution,[],[f3713,f83])).
% 2.15/0.70  fof(f83,plain,(
% 2.15/0.70    ( ! [X4,X3] : (k8_relat_1(X4,k6_relat_1(X3)) = k7_relat_1(k6_relat_1(X4),X3)) )),
% 2.15/0.70    inference(superposition,[],[f72,f70])).
% 2.15/0.70  fof(f70,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 2.15/0.70    inference(resolution,[],[f52,f39])).
% 2.15/0.70  fof(f39,plain,(
% 2.15/0.70    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.15/0.70    inference(cnf_transformation,[],[f5])).
% 2.15/0.70  fof(f5,axiom,(
% 2.15/0.70    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 2.15/0.70  fof(f52,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 2.15/0.70    inference(cnf_transformation,[],[f29])).
% 2.15/0.70  fof(f29,plain,(
% 2.15/0.70    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 2.15/0.70    inference(ennf_transformation,[],[f8])).
% 2.15/0.70  fof(f8,axiom,(
% 2.15/0.70    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 2.15/0.70  fof(f72,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.15/0.70    inference(resolution,[],[f53,f39])).
% 2.15/0.70  fof(f53,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f30])).
% 2.15/0.70  fof(f30,plain,(
% 2.15/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.15/0.70    inference(ennf_transformation,[],[f18])).
% 2.15/0.70  fof(f18,axiom,(
% 2.15/0.70    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.15/0.70  fof(f3713,plain,(
% 2.15/0.70    k8_relat_1(sK0,k6_relat_1(sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_2),
% 2.15/0.70    inference(superposition,[],[f80,f3064])).
% 2.15/0.70  fof(f3064,plain,(
% 2.15/0.70    ( ! [X10,X9] : (k7_relat_1(k6_relat_1(X10),X9) = k6_relat_1(k3_xboole_0(X10,X9))) )),
% 2.15/0.70    inference(superposition,[],[f2692,f1148])).
% 2.15/0.70  fof(f1148,plain,(
% 2.15/0.70    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 2.15/0.70    inference(superposition,[],[f1136,f246])).
% 2.15/0.70  fof(f246,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f236,f41])).
% 2.15/0.70  fof(f41,plain,(
% 2.15/0.70    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.15/0.70    inference(cnf_transformation,[],[f13])).
% 2.15/0.70  fof(f13,axiom,(
% 2.15/0.70    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.15/0.70  fof(f236,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X0) = k1_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))) )),
% 2.15/0.70    inference(superposition,[],[f98,f231])).
% 2.15/0.70  fof(f231,plain,(
% 2.15/0.70    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(k3_xboole_0(X1,X2)),X1)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f230,f40])).
% 2.15/0.70  fof(f40,plain,(
% 2.15/0.70    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 2.15/0.70    inference(cnf_transformation,[],[f14])).
% 2.15/0.70  fof(f14,axiom,(
% 2.15/0.70    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 2.15/0.70  fof(f230,plain,(
% 2.15/0.70    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(k3_xboole_0(X1,X2)),X1) = k4_relat_1(k6_relat_1(k3_xboole_0(X1,X2)))) )),
% 2.15/0.70    inference(superposition,[],[f222,f138])).
% 2.15/0.70  fof(f138,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 2.15/0.70    inference(resolution,[],[f136,f48])).
% 2.15/0.70  fof(f48,plain,(
% 2.15/0.70    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f1])).
% 2.15/0.70  fof(f1,axiom,(
% 2.15/0.70    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.15/0.70  fof(f136,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f135,f83])).
% 2.15/0.70  fof(f135,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) | ~r1_tarski(X0,X1)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f134,f70])).
% 2.15/0.70  fof(f134,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f131,f42])).
% 2.15/0.70  fof(f42,plain,(
% 2.15/0.70    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.15/0.70    inference(cnf_transformation,[],[f13])).
% 2.15/0.70  fof(f131,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 2.15/0.70    inference(resolution,[],[f56,f39])).
% 2.15/0.70  fof(f56,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 2.15/0.70    inference(cnf_transformation,[],[f34])).
% 2.15/0.70  fof(f34,plain,(
% 2.15/0.70    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.15/0.70    inference(flattening,[],[f33])).
% 2.15/0.70  fof(f33,plain,(
% 2.15/0.70    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.15/0.70    inference(ennf_transformation,[],[f15])).
% 2.15/0.70  fof(f15,axiom,(
% 2.15/0.70    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 2.15/0.70  fof(f222,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f221,f83])).
% 2.15/0.70  fof(f221,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f220,f70])).
% 2.15/0.70  fof(f220,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f219,f83])).
% 2.15/0.70  fof(f219,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f218,f70])).
% 2.15/0.70  fof(f218,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f215,f40])).
% 2.15/0.70  fof(f215,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) )),
% 2.15/0.70    inference(resolution,[],[f214,f39])).
% 2.15/0.70  fof(f214,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f211,f40])).
% 2.15/0.70  fof(f211,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) )),
% 2.15/0.70    inference(resolution,[],[f46,f39])).
% 2.15/0.70  fof(f46,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 2.15/0.70    inference(cnf_transformation,[],[f26])).
% 2.15/0.70  fof(f26,plain,(
% 2.15/0.70    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.15/0.70    inference(ennf_transformation,[],[f11])).
% 2.15/0.70  fof(f11,axiom,(
% 2.15/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 2.15/0.70  fof(f98,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f96,f41])).
% 2.15/0.70  fof(f96,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 2.15/0.70    inference(resolution,[],[f54,f39])).
% 2.15/0.70  fof(f54,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f31])).
% 2.15/0.70  fof(f31,plain,(
% 2.15/0.70    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.15/0.70    inference(ennf_transformation,[],[f17])).
% 2.15/0.70  fof(f17,axiom,(
% 2.15/0.70    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 2.15/0.70  fof(f1136,plain,(
% 2.15/0.70    ( ! [X6,X7] : (k3_xboole_0(k3_xboole_0(X6,X7),X6) = k3_xboole_0(X7,X6)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f1135,f699])).
% 2.15/0.70  fof(f699,plain,(
% 2.15/0.70    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k3_xboole_0(k3_xboole_0(X4,X5),X5)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f697,f98])).
% 2.15/0.70  fof(f697,plain,(
% 2.15/0.70    ( ! [X4,X5] : (k3_xboole_0(k3_xboole_0(X4,X5),X5) = k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) )),
% 2.15/0.70    inference(superposition,[],[f127,f675])).
% 2.15/0.70  fof(f675,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f674,f83])).
% 2.15/0.70  fof(f674,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f665,f70])).
% 2.15/0.70  fof(f665,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) )),
% 2.15/0.70    inference(superposition,[],[f663,f66])).
% 2.15/0.70  fof(f66,plain,(
% 2.15/0.70    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f64,f41])).
% 2.15/0.70  fof(f64,plain,(
% 2.15/0.70    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 2.15/0.70    inference(resolution,[],[f43,f39])).
% 2.15/0.70  fof(f43,plain,(
% 2.15/0.70    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 2.15/0.70    inference(cnf_transformation,[],[f23])).
% 2.15/0.70  fof(f23,plain,(
% 2.15/0.70    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.15/0.70    inference(ennf_transformation,[],[f19])).
% 2.15/0.70  fof(f19,axiom,(
% 2.15/0.70    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 2.15/0.70  fof(f663,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f662,f83])).
% 2.15/0.70  fof(f662,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k8_relat_1(X2,k6_relat_1(X0)),X1)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f659,f70])).
% 2.15/0.70  fof(f659,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X2)),X1)) )),
% 2.15/0.70    inference(resolution,[],[f226,f39])).
% 2.15/0.70  fof(f226,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) = k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2)) )),
% 2.15/0.70    inference(resolution,[],[f57,f39])).
% 2.15/0.70  fof(f57,plain,(
% 2.15/0.70    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f35])).
% 2.15/0.70  fof(f35,plain,(
% 2.15/0.70    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.15/0.70    inference(ennf_transformation,[],[f7])).
% 2.15/0.70  fof(f7,axiom,(
% 2.15/0.70    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 2.15/0.70  fof(f127,plain,(
% 2.15/0.70    ( ! [X14,X15,X13] : (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X13),X14),X15)) = k3_xboole_0(k3_xboole_0(X13,X14),X15)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f122,f98])).
% 2.15/0.70  fof(f122,plain,(
% 2.15/0.70    ( ! [X14,X15,X13] : (k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X13),X14),X15)) = k3_xboole_0(k1_relat_1(k7_relat_1(k6_relat_1(X13),X14)),X15)) )),
% 2.15/0.70    inference(resolution,[],[f116,f54])).
% 2.15/0.70  fof(f116,plain,(
% 2.15/0.70    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.15/0.70    inference(subsumption_resolution,[],[f114,f39])).
% 2.15/0.70  fof(f114,plain,(
% 2.15/0.70    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.15/0.70    inference(superposition,[],[f51,f113])).
% 2.15/0.70  fof(f113,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(X1,X0))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f112,f83])).
% 2.15/0.70  fof(f112,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(X1,X0))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f110,f41])).
% 2.15/0.70  fof(f110,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0))) )),
% 2.15/0.70    inference(resolution,[],[f55,f39])).
% 2.15/0.70  fof(f55,plain,(
% 2.15/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) )),
% 2.15/0.70    inference(cnf_transformation,[],[f32])).
% 2.15/0.70  fof(f32,plain,(
% 2.15/0.70    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.15/0.70    inference(ennf_transformation,[],[f9])).
% 2.15/0.70  fof(f9,axiom,(
% 2.15/0.70    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).
% 2.15/0.70  fof(f51,plain,(
% 2.15/0.70    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.15/0.70    inference(cnf_transformation,[],[f28])).
% 2.15/0.70  fof(f28,plain,(
% 2.15/0.70    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.15/0.70    inference(ennf_transformation,[],[f6])).
% 2.15/0.70  fof(f6,axiom,(
% 2.15/0.70    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 2.15/0.70  fof(f1135,plain,(
% 2.15/0.70    ( ! [X6,X7] : (k3_xboole_0(k3_xboole_0(k3_xboole_0(X6,X7),X7),X6) = k3_xboole_0(X7,X6)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f1125,f98])).
% 2.15/0.70  fof(f1125,plain,(
% 2.15/0.70    ( ! [X6,X7] : (k3_xboole_0(k3_xboole_0(k3_xboole_0(X6,X7),X7),X6) = k1_relat_1(k7_relat_1(k6_relat_1(X7),X6))) )),
% 2.15/0.70    inference(superposition,[],[f127,f771])).
% 2.15/0.70  fof(f771,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X1),X0)) )),
% 2.15/0.70    inference(superposition,[],[f672,f470])).
% 2.15/0.70  fof(f470,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k8_relat_1(k3_xboole_0(X0,X1),k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f462,f222])).
% 2.15/0.70  fof(f462,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k8_relat_1(k3_xboole_0(X0,X1),k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.15/0.70    inference(superposition,[],[f225,f126])).
% 2.15/0.70  fof(f126,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k3_xboole_0(X0,X1))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f117,f98])).
% 2.15/0.70  fof(f117,plain,(
% 2.15/0.70    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 2.15/0.70    inference(resolution,[],[f116,f43])).
% 2.15/0.70  fof(f225,plain,(
% 2.15/0.70    ( ! [X6,X7,X5] : (k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f224,f121])).
% 2.15/0.70  fof(f121,plain,(
% 2.15/0.70    ( ! [X12,X10,X11] : (k7_relat_1(k7_relat_1(k6_relat_1(X10),X11),X12) = k5_relat_1(k6_relat_1(X12),k7_relat_1(k6_relat_1(X10),X11))) )),
% 2.15/0.70    inference(resolution,[],[f116,f53])).
% 2.15/0.70  fof(f224,plain,(
% 2.15/0.70    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k8_relat_1(X5,k7_relat_1(k6_relat_1(X7),X6))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f223,f120])).
% 2.15/0.70  fof(f120,plain,(
% 2.15/0.70    ( ! [X8,X7,X9] : (k8_relat_1(X7,k7_relat_1(k6_relat_1(X8),X9)) = k5_relat_1(k7_relat_1(k6_relat_1(X8),X9),k6_relat_1(X7))) )),
% 2.15/0.70    inference(resolution,[],[f116,f52])).
% 2.15/0.70  fof(f223,plain,(
% 2.15/0.70    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f217,f222])).
% 2.15/0.70  fof(f217,plain,(
% 2.15/0.70    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))) )),
% 2.15/0.70    inference(resolution,[],[f214,f116])).
% 2.15/0.70  fof(f672,plain,(
% 2.15/0.70    ( ! [X4,X5,X3] : (k8_relat_1(X5,k7_relat_1(k6_relat_1(X3),X4)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X3),X4)) )),
% 2.15/0.70    inference(superposition,[],[f663,f120])).
% 2.15/0.70  fof(f2692,plain,(
% 2.15/0.70    ( ! [X23,X22] : (k7_relat_1(k6_relat_1(X22),X23) = k6_relat_1(k3_xboole_0(X23,X22))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f2691,f1336])).
% 2.15/0.70  fof(f1336,plain,(
% 2.15/0.70    ( ! [X41,X40] : (k7_relat_1(k6_relat_1(X41),X40) = k7_relat_1(k6_relat_1(k3_xboole_0(X41,X40)),X40)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f1244,f231])).
% 2.15/0.70  fof(f1244,plain,(
% 2.15/0.70    ( ! [X41,X40] : (k7_relat_1(k6_relat_1(X41),X40) = k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(X41,X40)),X41),X40)) )),
% 2.15/0.70    inference(superposition,[],[f771,f1148])).
% 2.15/0.70  fof(f2691,plain,(
% 2.15/0.70    ( ! [X23,X22] : (k6_relat_1(k3_xboole_0(X23,X22)) = k7_relat_1(k6_relat_1(k3_xboole_0(X22,X23)),X23)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f2614,f1197])).
% 2.15/0.70  fof(f1197,plain,(
% 2.15/0.70    ( ! [X50,X49] : (k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(X50,X49)),X49),k3_xboole_0(X49,X50)) = k6_relat_1(k3_xboole_0(X49,X50))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f1173,f138])).
% 2.15/0.70  fof(f1173,plain,(
% 2.15/0.70    ( ! [X50,X49] : (k7_relat_1(k6_relat_1(X49),k3_xboole_0(X49,X50)) = k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(X50,X49)),X49),k3_xboole_0(X49,X50))) )),
% 2.15/0.70    inference(superposition,[],[f771,f1136])).
% 2.15/0.70  fof(f2614,plain,(
% 2.15/0.70    ( ! [X23,X22] : (k7_relat_1(k6_relat_1(k3_xboole_0(X22,X23)),X23) = k7_relat_1(k7_relat_1(k6_relat_1(k3_xboole_0(X22,X23)),X23),k3_xboole_0(X23,X22))) )),
% 2.15/0.70    inference(superposition,[],[f126,f2317])).
% 2.15/0.70  fof(f2317,plain,(
% 2.15/0.70    ( ! [X87,X86] : (k3_xboole_0(X86,X87) = k3_xboole_0(k3_xboole_0(X87,X86),X86)) )),
% 2.15/0.70    inference(forward_demodulation,[],[f2316,f149])).
% 2.15/0.70  fof(f149,plain,(
% 2.15/0.70    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k3_xboole_0(X6,k3_xboole_0(X6,X7))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f147,f41])).
% 2.15/0.70  fof(f147,plain,(
% 2.15/0.70    ( ! [X6,X7] : (k3_xboole_0(X6,k3_xboole_0(X6,X7)) = k1_relat_1(k6_relat_1(k3_xboole_0(X6,X7)))) )),
% 2.15/0.70    inference(superposition,[],[f98,f138])).
% 2.15/0.70  fof(f2316,plain,(
% 2.15/0.70    ( ! [X87,X86] : (k3_xboole_0(k3_xboole_0(X87,X86),X86) = k3_xboole_0(X86,k3_xboole_0(X86,X87))) )),
% 2.15/0.70    inference(forward_demodulation,[],[f2262,f1148])).
% 2.15/0.70  fof(f2262,plain,(
% 2.15/0.70    ( ! [X87,X86] : (k3_xboole_0(k3_xboole_0(X87,X86),X86) = k3_xboole_0(k3_xboole_0(X86,X87),X86)) )),
% 2.15/0.70    inference(superposition,[],[f1136,f1212])).
% 2.15/0.70  fof(f1212,plain,(
% 2.15/0.70    ( ! [X8,X7] : (k3_xboole_0(X8,X7) = k3_xboole_0(X7,k3_xboole_0(X7,X8))) )),
% 2.15/0.70    inference(superposition,[],[f1148,f1136])).
% 2.15/0.70  fof(f80,plain,(
% 2.15/0.70    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) | spl2_2),
% 2.15/0.70    inference(avatar_component_clause,[],[f78])).
% 2.15/0.70  fof(f78,plain,(
% 2.15/0.70    spl2_2 <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k8_relat_1(sK0,k6_relat_1(sK1))),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.15/0.70  fof(f3849,plain,(
% 2.15/0.70    spl2_3),
% 2.15/0.70    inference(avatar_contradiction_clause,[],[f3848])).
% 2.15/0.70  fof(f3848,plain,(
% 2.15/0.70    $false | spl2_3),
% 2.15/0.70    inference(trivial_inequality_removal,[],[f3712])).
% 2.15/0.70  fof(f3712,plain,(
% 2.15/0.70    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_3),
% 2.15/0.70    inference(superposition,[],[f90,f3064])).
% 2.15/0.70  fof(f90,plain,(
% 2.15/0.70    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_3),
% 2.15/0.70    inference(avatar_component_clause,[],[f88])).
% 2.15/0.70  fof(f88,plain,(
% 2.15/0.70    spl2_3 <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.15/0.70  fof(f3383,plain,(
% 2.15/0.70    ~spl2_4 | spl2_3),
% 2.15/0.70    inference(avatar_split_clause,[],[f3110,f88,f3380])).
% 2.15/0.70  fof(f3380,plain,(
% 2.15/0.70    spl2_4 <=> k7_relat_1(k6_relat_1(sK0),sK1) = k7_relat_1(k6_relat_1(sK1),sK0)),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.15/0.70  fof(f3110,plain,(
% 2.15/0.70    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0) | spl2_3),
% 2.15/0.70    inference(superposition,[],[f90,f2692])).
% 2.15/0.70  fof(f91,plain,(
% 2.15/0.70    ~spl2_3 | spl2_1),
% 2.15/0.70    inference(avatar_split_clause,[],[f84,f60,f88])).
% 2.15/0.70  fof(f60,plain,(
% 2.15/0.70    spl2_1 <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.15/0.70    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.15/0.70  fof(f84,plain,(
% 2.15/0.70    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 2.15/0.70    inference(superposition,[],[f62,f72])).
% 2.15/0.70  fof(f62,plain,(
% 2.15/0.70    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 2.15/0.70    inference(avatar_component_clause,[],[f60])).
% 2.15/0.70  fof(f81,plain,(
% 2.15/0.70    ~spl2_2 | spl2_1),
% 2.15/0.70    inference(avatar_split_clause,[],[f75,f60,f78])).
% 2.15/0.70  fof(f75,plain,(
% 2.15/0.70    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) | spl2_1),
% 2.15/0.70    inference(superposition,[],[f62,f70])).
% 2.15/0.70  fof(f63,plain,(
% 2.15/0.70    ~spl2_1),
% 2.15/0.70    inference(avatar_split_clause,[],[f38,f60])).
% 2.15/0.70  fof(f38,plain,(
% 2.15/0.70    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.15/0.70    inference(cnf_transformation,[],[f37])).
% 2.15/0.70  fof(f37,plain,(
% 2.15/0.70    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.15/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f36])).
% 2.15/0.70  fof(f36,plain,(
% 2.15/0.70    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.15/0.70    introduced(choice_axiom,[])).
% 2.15/0.70  fof(f22,plain,(
% 2.15/0.70    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 2.15/0.70    inference(ennf_transformation,[],[f21])).
% 2.15/0.70  fof(f21,negated_conjecture,(
% 2.15/0.70    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.15/0.70    inference(negated_conjecture,[],[f20])).
% 2.15/0.70  fof(f20,conjecture,(
% 2.15/0.70    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.15/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 2.15/0.70  % SZS output end Proof for theBenchmark
% 2.15/0.70  % (5111)------------------------------
% 2.15/0.70  % (5111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.70  % (5111)Termination reason: Refutation
% 2.15/0.70  
% 2.15/0.70  % (5111)Memory used [KB]: 9338
% 2.15/0.70  % (5111)Time elapsed: 0.273 s
% 2.15/0.70  % (5111)------------------------------
% 2.15/0.70  % (5111)------------------------------
% 2.15/0.71  % (5110)Success in time 0.342 s
%------------------------------------------------------------------------------
