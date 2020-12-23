%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 (1643 expanded)
%              Number of leaves         :   23 ( 484 expanded)
%              Depth                    :   24
%              Number of atoms          :  194 (2528 expanded)
%              Number of equality atoms :  110 (1063 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2200,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2199])).

fof(f2199,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(superposition,[],[f2175,f1693])).

fof(f1693,plain,(
    ! [X15,X16] : k8_relat_1(X16,k6_relat_1(X15)) = k6_relat_1(k2_relat_1(k8_relat_1(X16,k6_relat_1(X15)))) ),
    inference(forward_demodulation,[],[f1585,f629])).

fof(f629,plain,(
    ! [X19,X20] : k8_relat_1(X20,k6_relat_1(X19)) = k8_relat_1(k2_relat_1(k8_relat_1(X20,k6_relat_1(X19))),k6_relat_1(X19)) ),
    inference(forward_demodulation,[],[f602,f131])).

fof(f131,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f130,f79])).

fof(f79,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f53,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f130,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f129,f79])).

fof(f129,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f126,f42])).

fof(f42,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f126,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f125,f41])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f122,f42])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f47,f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f602,plain,(
    ! [X19,X20] : k8_relat_1(k2_relat_1(k8_relat_1(X20,k6_relat_1(X19))),k6_relat_1(X19)) = k4_relat_1(k8_relat_1(X19,k6_relat_1(X20))) ),
    inference(superposition,[],[f131,f585])).

fof(f585,plain,(
    ! [X4,X5] : k8_relat_1(X5,k6_relat_1(X4)) = k8_relat_1(X5,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5))))) ),
    inference(forward_demodulation,[],[f584,f221])).

fof(f221,plain,(
    ! [X10,X11] : k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11)))) = k8_relat_1(X10,k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11))))) ),
    inference(forward_demodulation,[],[f210,f42])).

fof(f210,plain,(
    ! [X10,X11] : k8_relat_1(X10,k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11))))) = k4_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11))))) ),
    inference(superposition,[],[f131,f114])).

fof(f114,plain,(
    ! [X0,X1] : k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) ),
    inference(resolution,[],[f113,f92])).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X1) ),
    inference(forward_demodulation,[],[f91,f79])).

fof(f91,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),X1) ),
    inference(forward_demodulation,[],[f89,f44])).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),k2_relat_1(k6_relat_1(X1))) ),
    inference(resolution,[],[f87,f41])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)),k2_relat_1(X0)) ) ),
    inference(resolution,[],[f46,f41])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1)) ) ),
    inference(resolution,[],[f106,f41])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f105,f79])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f56,f43])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f584,plain,(
    ! [X4,X5] : k8_relat_1(X5,k8_relat_1(X4,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) = k8_relat_1(X5,k6_relat_1(X4)) ),
    inference(forward_demodulation,[],[f576,f131])).

fof(f576,plain,(
    ! [X4,X5] : k8_relat_1(X5,k8_relat_1(X4,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) = k4_relat_1(k8_relat_1(X4,k6_relat_1(X5))) ),
    inference(superposition,[],[f568,f439])).

fof(f439,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))),k8_relat_1(X2,k6_relat_1(X3))) ),
    inference(superposition,[],[f101,f100])).

fof(f100,plain,(
    ! [X10,X11,X9] : k8_relat_1(X9,k8_relat_1(X10,k6_relat_1(X11))) = k5_relat_1(k8_relat_1(X10,k6_relat_1(X11)),k6_relat_1(X9)) ),
    inference(resolution,[],[f96,f53])).

fof(f96,plain,(
    ! [X0,X1] : v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(resolution,[],[f95,f41])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f85,f41])).

fof(f85,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X2))
      | v1_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ) ),
    inference(superposition,[],[f58,f79])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f101,plain,(
    ! [X12,X13] : k8_relat_1(X12,k6_relat_1(X13)) = k5_relat_1(k8_relat_1(X12,k6_relat_1(X13)),k6_relat_1(k2_relat_1(k8_relat_1(X12,k6_relat_1(X13))))) ),
    inference(resolution,[],[f96,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f568,plain,(
    ! [X6,X7,X5] : k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6))) = k4_relat_1(k8_relat_1(X6,k8_relat_1(X7,k6_relat_1(X5)))) ),
    inference(forward_demodulation,[],[f567,f181])).

fof(f181,plain,(
    ! [X6,X8,X7] : k5_relat_1(k6_relat_1(X6),k8_relat_1(X7,k6_relat_1(X8))) = k8_relat_1(X7,k8_relat_1(X8,k6_relat_1(X6))) ),
    inference(backward_demodulation,[],[f99,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] : k7_relat_1(k8_relat_1(X0,k6_relat_1(X2)),X1) = k8_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f176,f79])).

fof(f176,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X2)),X1) ),
    inference(forward_demodulation,[],[f173,f99])).

fof(f173,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
    inference(resolution,[],[f153,f41])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),X0)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f57,f41])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

fof(f99,plain,(
    ! [X6,X8,X7] : k5_relat_1(k6_relat_1(X6),k8_relat_1(X7,k6_relat_1(X8))) = k7_relat_1(k8_relat_1(X7,k6_relat_1(X8)),X6) ),
    inference(resolution,[],[f96,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f567,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6))) ),
    inference(forward_demodulation,[],[f566,f100])).

fof(f566,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k8_relat_1(X7,k6_relat_1(X6)),k6_relat_1(X5)) ),
    inference(forward_demodulation,[],[f128,f131])).

fof(f128,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k4_relat_1(k8_relat_1(X6,k6_relat_1(X7))),k6_relat_1(X5)) ),
    inference(resolution,[],[f125,f96])).

fof(f1585,plain,(
    ! [X15,X16] : k6_relat_1(k2_relat_1(k8_relat_1(X16,k6_relat_1(X15)))) = k8_relat_1(k2_relat_1(k8_relat_1(X16,k6_relat_1(X15))),k6_relat_1(X15)) ),
    inference(superposition,[],[f114,f1568])).

fof(f1568,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X3,k6_relat_1(X2)) ),
    inference(superposition,[],[f1533,f131])).

fof(f1533,plain,(
    ! [X2,X1] : k8_relat_1(X1,k6_relat_1(X2)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(superposition,[],[f568,f1507])).

fof(f1507,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(resolution,[],[f890,f96])).

fof(f890,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))
      | k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0))) ) ),
    inference(forward_demodulation,[],[f883,f181])).

fof(f883,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X0),k8_relat_1(X0,k6_relat_1(X1)))
      | ~ v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f878,f56])).

fof(f878,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) ),
    inference(backward_demodulation,[],[f202,f872])).

fof(f872,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f871,f86])).

fof(f86,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f81,f79])).

fof(f81,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f54,f41])).

fof(f871,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f867,f43])).

fof(f867,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f866,f41])).

fof(f866,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(forward_demodulation,[],[f73,f72])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

% (31028)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f202,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f71,f72])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2175,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f880,f1814])).

fof(f1814,plain,(
    ! [X4,X5] : k2_relat_1(k8_relat_1(X4,k6_relat_1(X5))) = k1_relat_1(k8_relat_1(X4,k6_relat_1(X5))) ),
    inference(superposition,[],[f43,f1693])).

fof(f880,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f201,f872])).

fof(f201,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f103,f72])).

fof(f103,plain,(
    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f70,f79])).

fof(f70,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f40,f69])).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f38])).

fof(f38,plain,
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
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (31022)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (31037)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.46  % (31021)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (31032)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (31031)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (31031)Refutation not found, incomplete strategy% (31031)------------------------------
% 0.20/0.46  % (31031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (31036)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (31023)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (31035)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (31031)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (31031)Memory used [KB]: 10618
% 0.20/0.48  % (31031)Time elapsed: 0.050 s
% 0.20/0.48  % (31031)------------------------------
% 0.20/0.48  % (31031)------------------------------
% 0.20/0.48  % (31029)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (31024)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (31020)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (31034)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (31022)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f2200,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f2199])).
% 0.20/0.49  fof(f2199,plain,(
% 0.20/0.49    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.20/0.49    inference(superposition,[],[f2175,f1693])).
% 0.20/0.49  fof(f1693,plain,(
% 0.20/0.49    ( ! [X15,X16] : (k8_relat_1(X16,k6_relat_1(X15)) = k6_relat_1(k2_relat_1(k8_relat_1(X16,k6_relat_1(X15))))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f1585,f629])).
% 0.20/0.49  fof(f629,plain,(
% 0.20/0.49    ( ! [X19,X20] : (k8_relat_1(X20,k6_relat_1(X19)) = k8_relat_1(k2_relat_1(k8_relat_1(X20,k6_relat_1(X19))),k6_relat_1(X19))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f602,f131])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f130,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.49    inference(resolution,[],[f53,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f129,f79])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f126,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,axiom,(
% 0.20/0.49    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) )),
% 0.20/0.49    inference(resolution,[],[f125,f41])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f122,f42])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f47,f41])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.20/0.49  fof(f602,plain,(
% 0.20/0.49    ( ! [X19,X20] : (k8_relat_1(k2_relat_1(k8_relat_1(X20,k6_relat_1(X19))),k6_relat_1(X19)) = k4_relat_1(k8_relat_1(X19,k6_relat_1(X20)))) )),
% 0.20/0.49    inference(superposition,[],[f131,f585])).
% 0.20/0.49  fof(f585,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k8_relat_1(X5,k6_relat_1(X4)) = k8_relat_1(X5,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f584,f221])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    ( ! [X10,X11] : (k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11)))) = k8_relat_1(X10,k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11)))))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f210,f42])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    ( ! [X10,X11] : (k8_relat_1(X10,k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11))))) = k4_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11)))))) )),
% 0.20/0.49    inference(superposition,[],[f131,f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0))) )),
% 0.20/0.49    inference(resolution,[],[f113,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f91,f79])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f89,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))),k2_relat_1(k6_relat_1(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f87,f41])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(k5_relat_1(k6_relat_1(X1),X0)),k2_relat_1(X0))) )),
% 0.20/0.49    inference(resolution,[],[f46,f41])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.49    inference(resolution,[],[f106,f41])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f105,f79])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(superposition,[],[f56,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.20/0.49  fof(f584,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k8_relat_1(X5,k8_relat_1(X4,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) = k8_relat_1(X5,k6_relat_1(X4))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f576,f131])).
% 0.20/0.49  fof(f576,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k8_relat_1(X5,k8_relat_1(X4,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) = k4_relat_1(k8_relat_1(X4,k6_relat_1(X5)))) )),
% 0.20/0.49    inference(superposition,[],[f568,f439])).
% 0.20/0.49  fof(f439,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))),k8_relat_1(X2,k6_relat_1(X3)))) )),
% 0.20/0.49    inference(superposition,[],[f101,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (k8_relat_1(X9,k8_relat_1(X10,k6_relat_1(X11))) = k5_relat_1(k8_relat_1(X10,k6_relat_1(X11)),k6_relat_1(X9))) )),
% 0.20/0.49    inference(resolution,[],[f96,f53])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f95,f41])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f85,f41])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X2)) | v1_relat_1(k8_relat_1(X2,k6_relat_1(X1)))) )),
% 0.20/0.49    inference(superposition,[],[f58,f79])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X12,X13] : (k8_relat_1(X12,k6_relat_1(X13)) = k5_relat_1(k8_relat_1(X12,k6_relat_1(X13)),k6_relat_1(k2_relat_1(k8_relat_1(X12,k6_relat_1(X13)))))) )),
% 0.20/0.49    inference(resolution,[],[f96,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.49  fof(f568,plain,(
% 0.20/0.49    ( ! [X6,X7,X5] : (k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6))) = k4_relat_1(k8_relat_1(X6,k8_relat_1(X7,k6_relat_1(X5))))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f567,f181])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    ( ! [X6,X8,X7] : (k5_relat_1(k6_relat_1(X6),k8_relat_1(X7,k6_relat_1(X8))) = k8_relat_1(X7,k8_relat_1(X8,k6_relat_1(X6)))) )),
% 0.20/0.49    inference(backward_demodulation,[],[f99,f177])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,k6_relat_1(X2)),X1) = k8_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f176,f79])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X2)),X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f173,f99])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2)))) )),
% 0.20/0.49    inference(resolution,[],[f153,f41])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),X0)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,X0))) )),
% 0.20/0.49    inference(resolution,[],[f57,f41])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X6,X8,X7] : (k5_relat_1(k6_relat_1(X6),k8_relat_1(X7,k6_relat_1(X8))) = k7_relat_1(k8_relat_1(X7,k6_relat_1(X8)),X6)) )),
% 0.20/0.49    inference(resolution,[],[f96,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.49  fof(f567,plain,(
% 0.20/0.49    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f566,f100])).
% 0.20/0.49  fof(f566,plain,(
% 0.20/0.49    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k8_relat_1(X7,k6_relat_1(X6)),k6_relat_1(X5))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f128,f131])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k4_relat_1(k8_relat_1(X6,k6_relat_1(X7))),k6_relat_1(X5))) )),
% 0.20/0.49    inference(resolution,[],[f125,f96])).
% 0.20/0.49  fof(f1585,plain,(
% 0.20/0.49    ( ! [X15,X16] : (k6_relat_1(k2_relat_1(k8_relat_1(X16,k6_relat_1(X15)))) = k8_relat_1(k2_relat_1(k8_relat_1(X16,k6_relat_1(X15))),k6_relat_1(X15))) )),
% 0.20/0.49    inference(superposition,[],[f114,f1568])).
% 0.20/0.49  fof(f1568,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X3,k6_relat_1(X2))) )),
% 0.20/0.49    inference(superposition,[],[f1533,f131])).
% 0.20/0.49  fof(f1533,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k8_relat_1(X1,k6_relat_1(X2)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X2)))) )),
% 0.20/0.49    inference(superposition,[],[f568,f1507])).
% 0.20/0.49  fof(f1507,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.20/0.49    inference(resolution,[],[f890,f96])).
% 0.20/0.49  fof(f890,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) | k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f883,f181])).
% 0.20/0.49  fof(f883,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X0),k8_relat_1(X0,k6_relat_1(X1))) | ~v1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f878,f56])).
% 0.20/0.49  fof(f878,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0)) )),
% 0.20/0.49    inference(backward_demodulation,[],[f202,f872])).
% 0.20/0.49  fof(f872,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f871,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f81,f79])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 0.20/0.49    inference(resolution,[],[f54,f41])).
% 0.20/0.49  fof(f871,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f867,f43])).
% 0.20/0.49  fof(f867,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 0.20/0.49    inference(resolution,[],[f866,f41])).
% 0.20/0.49  fof(f866,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f73,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f52,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f50,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f51,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f59,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f60,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f61,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f62,f63])).
% 0.20/0.49  % (31028)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f55,f69])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.20/0.49    inference(backward_demodulation,[],[f71,f72])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f49,f69])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.49  fof(f2175,plain,(
% 0.20/0.49    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK0,k6_relat_1(sK1))))),
% 0.20/0.49    inference(backward_demodulation,[],[f880,f1814])).
% 0.20/0.49  fof(f1814,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k2_relat_1(k8_relat_1(X4,k6_relat_1(X5))) = k1_relat_1(k8_relat_1(X4,k6_relat_1(X5)))) )),
% 0.20/0.49    inference(superposition,[],[f43,f1693])).
% 0.20/0.49  fof(f880,plain,(
% 0.20/0.49    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1))))),
% 0.20/0.49    inference(backward_demodulation,[],[f201,f872])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.49    inference(backward_demodulation,[],[f103,f72])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.20/0.49    inference(forward_demodulation,[],[f70,f79])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 0.20/0.49    inference(definition_unfolding,[],[f40,f69])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f23])).
% 0.20/0.49  fof(f23,conjecture,(
% 0.20/0.49    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (31022)------------------------------
% 0.20/0.49  % (31022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31022)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (31022)Memory used [KB]: 7291
% 0.20/0.49  % (31022)Time elapsed: 0.095 s
% 0.20/0.49  % (31022)------------------------------
% 0.20/0.49  % (31022)------------------------------
% 0.20/0.49  % (31033)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (31018)Success in time 0.141 s
%------------------------------------------------------------------------------
