%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:26 EST 2020

% Result     : Theorem 10.89s
% Output     : Refutation 10.89s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 461 expanded)
%              Number of leaves         :   16 ( 127 expanded)
%              Depth                    :   28
%              Number of atoms          :  280 (1024 expanded)
%              Number of equality atoms :   74 ( 276 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25732,plain,(
    $false ),
    inference(subsumption_resolution,[],[f116,f25473])).

fof(f25473,plain,(
    ! [X30,X29] : k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k3_xboole_0(X30,X29)) ),
    inference(subsumption_resolution,[],[f25472,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f25472,plain,(
    ! [X30,X29] :
      ( ~ r1_tarski(k3_xboole_0(X30,X29),X30)
      | k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k3_xboole_0(X30,X29)) ) ),
    inference(forward_demodulation,[],[f25471,f133])).

fof(f133,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f124,f58])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f124,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f46,f56])).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f25471,plain,(
    ! [X30,X29] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X30),X29)),X30)
      | k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k3_xboole_0(X30,X29)) ) ),
    inference(forward_demodulation,[],[f25470,f5985])).

fof(f5985,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)) ),
    inference(subsumption_resolution,[],[f5969,f1743])).

fof(f1743,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f1715,f58])).

fof(f1715,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f475,f81])).

fof(f81,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f75,f58])).

fof(f75,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f54,f56])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f475,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k7_relat_1(k5_relat_1(X3,k6_relat_1(X4)),X2),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f474,f319])).

fof(f319,plain,(
    ! [X4,X3] :
      ( v1_relat_1(k5_relat_1(X3,k6_relat_1(X4)))
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,(
    ! [X4,X3] :
      ( v1_relat_1(k5_relat_1(X3,k6_relat_1(X4)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f298,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f298,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X6,X5)
      | v1_relat_1(X6)
      | ~ v1_relat_1(X5) ) ),
    inference(forward_demodulation,[],[f297,f56])).

fof(f297,plain,(
    ! [X6,X5] :
      ( v1_relat_1(X6)
      | ~ v1_relat_1(k1_relat_1(k6_relat_1(X5)))
      | ~ r1_tarski(X6,X5) ) ),
    inference(forward_demodulation,[],[f296,f56])).

fof(f296,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k1_relat_1(k6_relat_1(X6)))
      | ~ v1_relat_1(k1_relat_1(k6_relat_1(X5)))
      | ~ r1_tarski(X6,X5) ) ),
    inference(subsumption_resolution,[],[f285,f58])).

fof(f285,plain,(
    ! [X6,X5] :
      ( v1_relat_1(k1_relat_1(k6_relat_1(X6)))
      | ~ v1_relat_1(k1_relat_1(k6_relat_1(X5)))
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ r1_tarski(X6,X5) ) ),
    inference(superposition,[],[f131,f151])).

fof(f151,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X2) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f150,f57])).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f150,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X2) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X2)),X3) ) ),
    inference(subsumption_resolution,[],[f149,f58])).

fof(f149,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X2) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X2)),X3)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(subsumption_resolution,[],[f138,f58])).

fof(f138,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X2) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X2)),X3)
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f50,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f131,plain,(
    ! [X8,X9] :
      ( v1_relat_1(k1_relat_1(k7_relat_1(X8,X9)))
      | ~ v1_relat_1(k1_relat_1(X8))
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f47,f46])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f474,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k7_relat_1(k5_relat_1(X3,k6_relat_1(X4)),X2),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) ) ),
    inference(subsumption_resolution,[],[f448,f58])).

fof(f448,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k7_relat_1(k5_relat_1(X3,k6_relat_1(X4)),X2),k5_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) ) ),
    inference(superposition,[],[f195,f53])).

fof(f195,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k5_relat_1(X6,k5_relat_1(X7,k6_relat_1(X8))),k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f194,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f194,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k5_relat_1(X6,k5_relat_1(X7,k6_relat_1(X8))),k5_relat_1(X6,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f172,f58])).

fof(f172,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k5_relat_1(X6,k5_relat_1(X7,k6_relat_1(X8))),k5_relat_1(X6,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(k6_relat_1(X8))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f51,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f5969,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))) ) ),
    inference(resolution,[],[f1818,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1818,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f1790,f58])).

fof(f1790,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)),k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f480,f81])).

fof(f480,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X4),k5_relat_1(X5,k6_relat_1(X6))),k7_relat_1(X5,X4))
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f459,f58])).

fof(f459,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X4),k5_relat_1(X5,k6_relat_1(X6))),k7_relat_1(X5,X4))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(duplicate_literal_removal,[],[f452])).

fof(f452,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X4),k5_relat_1(X5,k6_relat_1(X6))),k7_relat_1(X5,X4))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(k6_relat_1(X4))
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f195,f53])).

fof(f25470,plain,(
    ! [X30,X29] :
      ( ~ r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))),X30)
      | k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k3_xboole_0(X30,X29)) ) ),
    inference(forward_demodulation,[],[f25469,f57])).

fof(f25469,plain,(
    ! [X30,X29] :
      ( k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k3_xboole_0(X30,X29))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))),X30) ) ),
    inference(forward_demodulation,[],[f25468,f133])).

fof(f25468,plain,(
    ! [X30,X29] :
      ( k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X30),X29)))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))),X30) ) ),
    inference(forward_demodulation,[],[f25467,f5985])).

fof(f25467,plain,(
    ! [X30,X29] :
      ( k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))),X30) ) ),
    inference(subsumption_resolution,[],[f25466,f58])).

fof(f25466,plain,(
    ! [X30,X29] :
      ( k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))),X30)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))) ) ),
    inference(subsumption_resolution,[],[f25099,f58])).

fof(f25099,plain,(
    ! [X30,X29] :
      ( k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))
      | ~ v1_relat_1(k6_relat_1(X30))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))),X30)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))) ) ),
    inference(superposition,[],[f25042,f50])).

fof(f25042,plain,(
    ! [X6,X5] :
      ( k5_relat_1(k6_relat_1(X5),X6) = k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))),X6)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f849,f1881])).

fof(f1881,plain,(
    ! [X10,X11] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X10),X11)),X10)
      | ~ v1_relat_1(X11) ) ),
    inference(subsumption_resolution,[],[f1864,f317])).

fof(f317,plain,(
    ! [X10,X9] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(X9),X10))
      | ~ v1_relat_1(X10) ) ),
    inference(duplicate_literal_removal,[],[f312])).

fof(f312,plain,(
    ! [X10,X9] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(X9),X10))
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f298,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1864,plain,(
    ! [X10,X11] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X10),X11)),X10)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X10),X11))
      | ~ v1_relat_1(X11) ) ),
    inference(superposition,[],[f128,f567])).

fof(f567,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f566,f57])).

fof(f566,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f565,f317])).

fof(f565,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1)) ) ),
    inference(subsumption_resolution,[],[f535,f58])).

fof(f535,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1)) ) ),
    inference(superposition,[],[f184,f53])).

fof(f184,plain,(
    ! [X8,X7] :
      ( k5_relat_1(X7,k5_relat_1(k6_relat_1(k2_relat_1(X7)),X8)) = k5_relat_1(X7,X8)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f177,f58])).

fof(f177,plain,(
    ! [X8,X7] :
      ( k5_relat_1(X7,k5_relat_1(k6_relat_1(k2_relat_1(X7)),X8)) = k5_relat_1(X7,X8)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(X7)))
      | ~ v1_relat_1(X7) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X8,X7] :
      ( k5_relat_1(X7,k5_relat_1(k6_relat_1(k2_relat_1(X7)),X8)) = k5_relat_1(X7,X8)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(X7)))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f45,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f128,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X2,X3)),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f63,f46])).

fof(f63,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f849,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6)),X5)
      | k5_relat_1(k6_relat_1(X5),X6) = k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))),X6)
      | ~ v1_relat_1(X6) ) ),
    inference(forward_demodulation,[],[f848,f57])).

fof(f848,plain,(
    ! [X6,X5] :
      ( k5_relat_1(k6_relat_1(X5),X6) = k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))),X6)
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6)))),X5) ) ),
    inference(subsumption_resolution,[],[f847,f317])).

fof(f847,plain,(
    ! [X6,X5] :
      ( k5_relat_1(k6_relat_1(X5),X6) = k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))),X6)
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6)))),X5)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),X6)) ) ),
    inference(subsumption_resolution,[],[f790,f58])).

fof(f790,plain,(
    ! [X6,X5] :
      ( k5_relat_1(k6_relat_1(X5),X6) = k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))),X6)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6)))),X5)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),X6)) ) ),
    inference(superposition,[],[f185,f54])).

fof(f185,plain,(
    ! [X10,X11,X9] :
      ( k5_relat_1(X9,k5_relat_1(k6_relat_1(X10),X11)) = k5_relat_1(X9,X11)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X9)
      | ~ r1_tarski(k2_relat_1(X9),X10) ) ),
    inference(subsumption_resolution,[],[f176,f58])).

fof(f176,plain,(
    ! [X10,X11,X9] :
      ( k5_relat_1(X9,k5_relat_1(k6_relat_1(X10),X11)) = k5_relat_1(X9,X11)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(k6_relat_1(X10))
      | ~ v1_relat_1(X9)
      | ~ r1_tarski(k2_relat_1(X9),X10) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X10,X11,X9] :
      ( k5_relat_1(X9,k5_relat_1(k6_relat_1(X10),X11)) = k5_relat_1(X9,X11)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(k6_relat_1(X10))
      | ~ v1_relat_1(X9)
      | ~ r1_tarski(k2_relat_1(X9),X10)
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f45,f50])).

fof(f116,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(subsumption_resolution,[],[f101,f58])).

fof(f101,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f40,f53])).

fof(f40,plain,(
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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:28:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (32244)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (32263)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (32263)Refutation not found, incomplete strategy% (32263)------------------------------
% 0.22/0.54  % (32263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32263)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32263)Memory used [KB]: 6140
% 0.22/0.54  % (32263)Time elapsed: 0.117 s
% 0.22/0.54  % (32263)------------------------------
% 0.22/0.54  % (32263)------------------------------
% 0.22/0.54  % (32241)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (32240)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (32257)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (32248)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (32260)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (32249)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (32239)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (32259)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (32239)Refutation not found, incomplete strategy% (32239)------------------------------
% 0.22/0.55  % (32239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32239)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32239)Memory used [KB]: 1663
% 0.22/0.55  % (32239)Time elapsed: 0.129 s
% 0.22/0.55  % (32239)------------------------------
% 0.22/0.55  % (32239)------------------------------
% 0.22/0.55  % (32264)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (32247)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (32256)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (32249)Refutation not found, incomplete strategy% (32249)------------------------------
% 0.22/0.55  % (32249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32249)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32249)Memory used [KB]: 6140
% 0.22/0.55  % (32249)Time elapsed: 0.133 s
% 0.22/0.55  % (32249)------------------------------
% 0.22/0.55  % (32249)------------------------------
% 0.22/0.55  % (32264)Refutation not found, incomplete strategy% (32264)------------------------------
% 0.22/0.55  % (32264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32264)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32264)Memory used [KB]: 6140
% 0.22/0.55  % (32264)Time elapsed: 0.133 s
% 0.22/0.55  % (32264)------------------------------
% 0.22/0.55  % (32264)------------------------------
% 0.22/0.55  % (32256)Refutation not found, incomplete strategy% (32256)------------------------------
% 0.22/0.55  % (32256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32256)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32256)Memory used [KB]: 1663
% 0.22/0.55  % (32256)Time elapsed: 0.132 s
% 0.22/0.55  % (32256)------------------------------
% 0.22/0.55  % (32256)------------------------------
% 0.22/0.55  % (32243)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (32258)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (32253)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (32248)Refutation not found, incomplete strategy% (32248)------------------------------
% 0.22/0.55  % (32248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32248)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32248)Memory used [KB]: 10618
% 0.22/0.55  % (32248)Time elapsed: 0.134 s
% 0.22/0.55  % (32248)------------------------------
% 0.22/0.55  % (32248)------------------------------
% 0.22/0.55  % (32252)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (32252)Refutation not found, incomplete strategy% (32252)------------------------------
% 0.22/0.55  % (32252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32252)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32252)Memory used [KB]: 1663
% 0.22/0.55  % (32252)Time elapsed: 0.128 s
% 0.22/0.55  % (32252)------------------------------
% 0.22/0.55  % (32252)------------------------------
% 0.22/0.56  % (32262)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (32262)Refutation not found, incomplete strategy% (32262)------------------------------
% 0.22/0.56  % (32262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32262)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32262)Memory used [KB]: 10618
% 0.22/0.56  % (32262)Time elapsed: 0.133 s
% 0.22/0.56  % (32262)------------------------------
% 0.22/0.56  % (32262)------------------------------
% 0.22/0.56  % (32255)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (32255)Refutation not found, incomplete strategy% (32255)------------------------------
% 0.22/0.56  % (32255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32255)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32255)Memory used [KB]: 1663
% 0.22/0.56  % (32255)Time elapsed: 0.133 s
% 0.22/0.56  % (32255)------------------------------
% 0.22/0.56  % (32255)------------------------------
% 0.22/0.56  % (32266)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (32245)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (32265)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (32251)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (32246)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (32265)Refutation not found, incomplete strategy% (32265)------------------------------
% 0.22/0.56  % (32265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (32265)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32265)Memory used [KB]: 6140
% 0.22/0.56  % (32265)Time elapsed: 0.141 s
% 0.22/0.56  % (32265)------------------------------
% 0.22/0.56  % (32265)------------------------------
% 0.22/0.57  % (32250)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (32250)Refutation not found, incomplete strategy% (32250)------------------------------
% 0.22/0.57  % (32250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (32250)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (32250)Memory used [KB]: 10618
% 0.22/0.57  % (32250)Time elapsed: 0.143 s
% 0.22/0.57  % (32250)------------------------------
% 0.22/0.57  % (32250)------------------------------
% 0.22/0.57  % (32267)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (32254)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.57  % (32267)Refutation not found, incomplete strategy% (32267)------------------------------
% 0.22/0.57  % (32267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (32267)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (32267)Memory used [KB]: 1663
% 0.22/0.57  % (32267)Time elapsed: 0.002 s
% 0.22/0.57  % (32267)------------------------------
% 0.22/0.57  % (32267)------------------------------
% 0.22/0.57  % (32242)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.57  % (32238)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.57  % (32254)Refutation not found, incomplete strategy% (32254)------------------------------
% 0.22/0.57  % (32254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (32254)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (32254)Memory used [KB]: 10618
% 0.22/0.57  % (32254)Time elapsed: 0.151 s
% 0.22/0.57  % (32254)------------------------------
% 0.22/0.57  % (32254)------------------------------
% 0.22/0.57  % (32261)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.69/0.58  % (32266)Refutation not found, incomplete strategy% (32266)------------------------------
% 1.69/0.58  % (32266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (32266)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.58  
% 1.69/0.58  % (32266)Memory used [KB]: 10618
% 1.69/0.58  % (32266)Time elapsed: 0.162 s
% 1.69/0.58  % (32266)------------------------------
% 1.69/0.58  % (32266)------------------------------
% 2.00/0.67  % (32293)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.00/0.67  % (32293)Refutation not found, incomplete strategy% (32293)------------------------------
% 2.00/0.67  % (32293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.67  % (32285)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.00/0.67  % (32293)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.67  
% 2.00/0.67  % (32293)Memory used [KB]: 1663
% 2.00/0.67  % (32293)Time elapsed: 0.086 s
% 2.00/0.67  % (32293)------------------------------
% 2.00/0.67  % (32293)------------------------------
% 2.00/0.68  % (32241)Refutation not found, incomplete strategy% (32241)------------------------------
% 2.00/0.68  % (32241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (32288)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.00/0.68  % (32240)Refutation not found, incomplete strategy% (32240)------------------------------
% 2.00/0.68  % (32240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.68  % (32240)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.68  
% 2.00/0.68  % (32240)Memory used [KB]: 6140
% 2.00/0.68  % (32240)Time elapsed: 0.238 s
% 2.00/0.68  % (32240)------------------------------
% 2.00/0.68  % (32240)------------------------------
% 2.00/0.68  % (32297)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.00/0.69  % (32287)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.00/0.69  % (32313)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.00/0.69  % (32292)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.00/0.69  % (32292)Refutation not found, incomplete strategy% (32292)------------------------------
% 2.00/0.69  % (32292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.69  % (32292)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.69  
% 2.00/0.69  % (32292)Memory used [KB]: 10618
% 2.00/0.69  % (32292)Time elapsed: 0.109 s
% 2.00/0.69  % (32292)------------------------------
% 2.00/0.69  % (32292)------------------------------
% 2.00/0.69  % (32241)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.69  
% 2.00/0.69  % (32241)Memory used [KB]: 6140
% 2.00/0.69  % (32241)Time elapsed: 0.247 s
% 2.00/0.69  % (32241)------------------------------
% 2.00/0.69  % (32241)------------------------------
% 2.00/0.69  % (32295)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.00/0.69  % (32291)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.00/0.70  % (32313)Refutation not found, incomplete strategy% (32313)------------------------------
% 2.00/0.70  % (32313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.70  % (32313)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.70  
% 2.00/0.70  % (32313)Memory used [KB]: 10618
% 2.00/0.70  % (32313)Time elapsed: 0.071 s
% 2.00/0.70  % (32313)------------------------------
% 2.00/0.70  % (32313)------------------------------
% 2.00/0.70  % (32299)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.00/0.70  % (32303)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.00/0.70  % (32253)Refutation not found, incomplete strategy% (32253)------------------------------
% 2.00/0.70  % (32253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.70  % (32253)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.70  
% 2.00/0.70  % (32253)Memory used [KB]: 6140
% 2.00/0.70  % (32253)Time elapsed: 0.243 s
% 2.00/0.70  % (32253)------------------------------
% 2.00/0.70  % (32253)------------------------------
% 2.00/0.70  % (32295)Refutation not found, incomplete strategy% (32295)------------------------------
% 2.00/0.70  % (32295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.70  % (32295)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.70  
% 2.00/0.70  % (32295)Memory used [KB]: 10618
% 2.00/0.70  % (32295)Time elapsed: 0.117 s
% 2.00/0.70  % (32295)------------------------------
% 2.00/0.70  % (32295)------------------------------
% 2.00/0.71  % (32302)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.00/0.71  % (32302)Refutation not found, incomplete strategy% (32302)------------------------------
% 2.00/0.71  % (32302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.71  % (32302)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.71  
% 2.00/0.71  % (32302)Memory used [KB]: 10618
% 2.00/0.71  % (32302)Time elapsed: 0.108 s
% 2.00/0.71  % (32302)------------------------------
% 2.00/0.71  % (32302)------------------------------
% 2.00/0.71  % (32304)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.00/0.71  % (32246)Refutation not found, incomplete strategy% (32246)------------------------------
% 2.00/0.71  % (32246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.71  % (32304)Refutation not found, incomplete strategy% (32304)------------------------------
% 2.00/0.71  % (32304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.71  % (32246)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.71  
% 2.00/0.71  % (32246)Memory used [KB]: 6140
% 2.00/0.71  % (32246)Time elapsed: 0.277 s
% 2.00/0.71  % (32246)------------------------------
% 2.00/0.71  % (32246)------------------------------
% 2.00/0.71  % (32291)Refutation not found, incomplete strategy% (32291)------------------------------
% 2.00/0.71  % (32291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.71  % (32291)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.71  
% 2.00/0.71  % (32291)Memory used [KB]: 10618
% 2.00/0.71  % (32291)Time elapsed: 0.128 s
% 2.00/0.71  % (32291)------------------------------
% 2.00/0.71  % (32291)------------------------------
% 2.00/0.71  % (32304)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.71  
% 2.00/0.71  % (32304)Memory used [KB]: 10618
% 2.00/0.71  % (32304)Time elapsed: 0.119 s
% 2.00/0.71  % (32304)------------------------------
% 2.00/0.71  % (32304)------------------------------
% 2.00/0.72  % (32311)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.76/0.80  % (32360)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.76/0.80  % (32356)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.14/0.80  % (32374)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 3.14/0.81  % (32363)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.14/0.82  % (32367)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.14/0.84  % (32381)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.14/0.84  % (32299)Refutation not found, incomplete strategy% (32299)------------------------------
% 3.14/0.84  % (32299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.84  % (32299)Termination reason: Refutation not found, incomplete strategy
% 3.14/0.84  
% 3.14/0.84  % (32299)Memory used [KB]: 6268
% 3.14/0.84  % (32299)Time elapsed: 0.245 s
% 3.14/0.84  % (32299)------------------------------
% 3.14/0.84  % (32299)------------------------------
% 3.14/0.84  % (32380)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.14/0.85  % (32380)Refutation not found, incomplete strategy% (32380)------------------------------
% 3.14/0.85  % (32380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.85  % (32380)Termination reason: Refutation not found, incomplete strategy
% 3.14/0.85  
% 3.14/0.85  % (32380)Memory used [KB]: 1663
% 3.14/0.85  % (32380)Time elapsed: 0.127 s
% 3.14/0.85  % (32380)------------------------------
% 3.14/0.85  % (32380)------------------------------
% 3.53/0.88  % (32356)Refutation not found, incomplete strategy% (32356)------------------------------
% 3.53/0.88  % (32356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.90  % (32356)Termination reason: Refutation not found, incomplete strategy
% 3.53/0.90  
% 3.53/0.90  % (32356)Memory used [KB]: 6140
% 3.53/0.90  % (32356)Time elapsed: 0.182 s
% 3.53/0.90  % (32356)------------------------------
% 3.53/0.90  % (32356)------------------------------
% 3.53/0.91  % (32360)Refutation not found, incomplete strategy% (32360)------------------------------
% 3.53/0.91  % (32360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.91  % (32360)Termination reason: Refutation not found, incomplete strategy
% 3.53/0.91  
% 3.53/0.91  % (32360)Memory used [KB]: 6140
% 3.53/0.91  % (32360)Time elapsed: 0.162 s
% 3.53/0.91  % (32360)------------------------------
% 3.53/0.91  % (32360)------------------------------
% 3.53/0.93  % (32244)Time limit reached!
% 3.53/0.93  % (32244)------------------------------
% 3.53/0.93  % (32244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.93  % (32244)Termination reason: Time limit
% 3.53/0.93  % (32244)Termination phase: Saturation
% 3.53/0.93  
% 3.53/0.93  % (32244)Memory used [KB]: 16630
% 3.53/0.93  % (32244)Time elapsed: 0.500 s
% 3.53/0.93  % (32244)------------------------------
% 3.53/0.93  % (32244)------------------------------
% 4.63/1.07  % (32245)Time limit reached!
% 4.63/1.07  % (32245)------------------------------
% 4.63/1.07  % (32245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.07  % (32245)Termination reason: Time limit
% 4.63/1.07  
% 4.63/1.07  % (32245)Memory used [KB]: 8315
% 4.63/1.07  % (32245)Time elapsed: 0.605 s
% 4.63/1.07  % (32245)------------------------------
% 4.63/1.07  % (32245)------------------------------
% 4.63/1.11  % (32367)Time limit reached!
% 4.63/1.11  % (32367)------------------------------
% 4.63/1.11  % (32367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.11  % (32367)Termination reason: Time limit
% 4.63/1.11  
% 4.63/1.11  % (32367)Memory used [KB]: 9978
% 4.63/1.11  % (32367)Time elapsed: 0.402 s
% 4.63/1.11  % (32367)------------------------------
% 4.63/1.11  % (32367)------------------------------
% 5.38/1.14  % (32381)Time limit reached!
% 5.38/1.14  % (32381)------------------------------
% 5.38/1.14  % (32381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.38/1.14  % (32381)Termination reason: Time limit
% 5.38/1.14  % (32381)Termination phase: Saturation
% 5.38/1.14  
% 5.38/1.14  % (32381)Memory used [KB]: 9850
% 5.38/1.14  % (32381)Time elapsed: 0.400 s
% 5.38/1.14  % (32381)------------------------------
% 5.38/1.14  % (32381)------------------------------
% 5.96/1.25  % (32363)Time limit reached!
% 5.96/1.25  % (32363)------------------------------
% 5.96/1.25  % (32363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.96/1.27  % (32363)Termination reason: Time limit
% 5.96/1.27  
% 5.96/1.27  % (32363)Memory used [KB]: 13176
% 5.96/1.27  % (32363)Time elapsed: 0.518 s
% 5.96/1.27  % (32363)------------------------------
% 5.96/1.27  % (32363)------------------------------
% 8.07/1.40  % (32288)Time limit reached!
% 8.07/1.40  % (32288)------------------------------
% 8.07/1.40  % (32288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.30/1.41  % (32288)Termination reason: Time limit
% 8.30/1.41  % (32288)Termination phase: Saturation
% 8.30/1.41  
% 8.30/1.41  % (32288)Memory used [KB]: 17142
% 8.30/1.41  % (32288)Time elapsed: 0.800 s
% 8.30/1.41  % (32288)------------------------------
% 8.30/1.41  % (32288)------------------------------
% 9.77/1.66  % (32238)Time limit reached!
% 9.77/1.66  % (32238)------------------------------
% 9.77/1.66  % (32238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.77/1.66  % (32238)Termination reason: Time limit
% 9.77/1.66  
% 9.77/1.66  % (32238)Memory used [KB]: 13560
% 9.77/1.66  % (32238)Time elapsed: 1.210 s
% 9.77/1.66  % (32238)------------------------------
% 9.77/1.66  % (32238)------------------------------
% 10.89/1.73  % (32243)Time limit reached!
% 10.89/1.73  % (32243)------------------------------
% 10.89/1.73  % (32243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.89/1.74  % (32243)Termination reason: Time limit
% 10.89/1.74  
% 10.89/1.74  % (32243)Memory used [KB]: 15607
% 10.89/1.74  % (32243)Time elapsed: 1.311 s
% 10.89/1.74  % (32243)------------------------------
% 10.89/1.74  % (32243)------------------------------
% 10.89/1.77  % (32297)Refutation found. Thanks to Tanya!
% 10.89/1.77  % SZS status Theorem for theBenchmark
% 10.89/1.77  % SZS output start Proof for theBenchmark
% 10.89/1.77  fof(f25732,plain,(
% 10.89/1.77    $false),
% 10.89/1.77    inference(subsumption_resolution,[],[f116,f25473])).
% 10.89/1.77  fof(f25473,plain,(
% 10.89/1.77    ( ! [X30,X29] : (k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k3_xboole_0(X30,X29))) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f25472,f48])).
% 10.89/1.77  fof(f48,plain,(
% 10.89/1.77    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 10.89/1.77    inference(cnf_transformation,[],[f3])).
% 10.89/1.77  fof(f3,axiom,(
% 10.89/1.77    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 10.89/1.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 10.89/1.77  fof(f25472,plain,(
% 10.89/1.77    ( ! [X30,X29] : (~r1_tarski(k3_xboole_0(X30,X29),X30) | k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k3_xboole_0(X30,X29))) )),
% 10.89/1.77    inference(forward_demodulation,[],[f25471,f133])).
% 10.89/1.77  fof(f133,plain,(
% 10.89/1.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f124,f58])).
% 10.89/1.77  fof(f58,plain,(
% 10.89/1.77    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 10.89/1.77    inference(cnf_transformation,[],[f9])).
% 10.89/1.77  fof(f9,axiom,(
% 10.89/1.77    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 10.89/1.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 10.89/1.77  fof(f124,plain,(
% 10.89/1.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 10.89/1.77    inference(superposition,[],[f46,f56])).
% 10.89/1.77  fof(f56,plain,(
% 10.89/1.77    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 10.89/1.77    inference(cnf_transformation,[],[f12])).
% 10.89/1.77  fof(f12,axiom,(
% 10.89/1.77    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 10.89/1.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 10.89/1.77  fof(f46,plain,(
% 10.89/1.77    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 10.89/1.77    inference(cnf_transformation,[],[f24])).
% 10.89/1.77  fof(f24,plain,(
% 10.89/1.77    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 10.89/1.77    inference(ennf_transformation,[],[f17])).
% 10.89/1.77  fof(f17,axiom,(
% 10.89/1.77    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 10.89/1.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 10.89/1.77  fof(f25471,plain,(
% 10.89/1.77    ( ! [X30,X29] : (~r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X30),X29)),X30) | k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k3_xboole_0(X30,X29))) )),
% 10.89/1.77    inference(forward_demodulation,[],[f25470,f5985])).
% 10.89/1.77  fof(f5985,plain,(
% 10.89/1.77    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f5969,f1743])).
% 10.89/1.77  fof(f1743,plain,(
% 10.89/1.77    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f1715,f58])).
% 10.89/1.77  fof(f1715,plain,(
% 10.89/1.77    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 10.89/1.77    inference(superposition,[],[f475,f81])).
% 10.89/1.77  fof(f81,plain,(
% 10.89/1.77    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f75,f58])).
% 10.89/1.77  fof(f75,plain,(
% 10.89/1.77    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 10.89/1.77    inference(superposition,[],[f54,f56])).
% 10.89/1.77  fof(f54,plain,(
% 10.89/1.77    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 10.89/1.77    inference(cnf_transformation,[],[f32])).
% 10.89/1.77  fof(f32,plain,(
% 10.89/1.77    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 10.89/1.77    inference(ennf_transformation,[],[f14])).
% 10.89/1.77  fof(f14,axiom,(
% 10.89/1.77    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 10.89/1.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 10.89/1.77  fof(f475,plain,(
% 10.89/1.77    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k5_relat_1(X3,k6_relat_1(X4)),X2),k5_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X3)) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f474,f319])).
% 10.89/1.77  fof(f319,plain,(
% 10.89/1.77    ( ! [X4,X3] : (v1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) | ~v1_relat_1(X3)) )),
% 10.89/1.77    inference(duplicate_literal_removal,[],[f309])).
% 10.89/1.77  fof(f309,plain,(
% 10.89/1.77    ( ! [X4,X3] : (v1_relat_1(k5_relat_1(X3,k6_relat_1(X4))) | ~v1_relat_1(X3) | ~v1_relat_1(X3)) )),
% 10.89/1.77    inference(resolution,[],[f298,f51])).
% 10.89/1.77  fof(f51,plain,(
% 10.89/1.77    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 10.89/1.77    inference(cnf_transformation,[],[f30])).
% 10.89/1.77  fof(f30,plain,(
% 10.89/1.77    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 10.89/1.77    inference(ennf_transformation,[],[f13])).
% 10.89/1.77  fof(f13,axiom,(
% 10.89/1.77    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 10.89/1.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 10.89/1.77  fof(f298,plain,(
% 10.89/1.77    ( ! [X6,X5] : (~r1_tarski(X6,X5) | v1_relat_1(X6) | ~v1_relat_1(X5)) )),
% 10.89/1.77    inference(forward_demodulation,[],[f297,f56])).
% 10.89/1.77  fof(f297,plain,(
% 10.89/1.77    ( ! [X6,X5] : (v1_relat_1(X6) | ~v1_relat_1(k1_relat_1(k6_relat_1(X5))) | ~r1_tarski(X6,X5)) )),
% 10.89/1.77    inference(forward_demodulation,[],[f296,f56])).
% 10.89/1.77  fof(f296,plain,(
% 10.89/1.77    ( ! [X6,X5] : (v1_relat_1(k1_relat_1(k6_relat_1(X6))) | ~v1_relat_1(k1_relat_1(k6_relat_1(X5))) | ~r1_tarski(X6,X5)) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f285,f58])).
% 10.89/1.77  fof(f285,plain,(
% 10.89/1.77    ( ! [X6,X5] : (v1_relat_1(k1_relat_1(k6_relat_1(X6))) | ~v1_relat_1(k1_relat_1(k6_relat_1(X5))) | ~v1_relat_1(k6_relat_1(X5)) | ~r1_tarski(X6,X5)) )),
% 10.89/1.77    inference(superposition,[],[f131,f151])).
% 10.89/1.77  fof(f151,plain,(
% 10.89/1.77    ( ! [X2,X3] : (k6_relat_1(X2) = k7_relat_1(k6_relat_1(X3),X2) | ~r1_tarski(X2,X3)) )),
% 10.89/1.77    inference(forward_demodulation,[],[f150,f57])).
% 10.89/1.77  fof(f57,plain,(
% 10.89/1.77    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 10.89/1.77    inference(cnf_transformation,[],[f12])).
% 10.89/1.77  fof(f150,plain,(
% 10.89/1.77    ( ! [X2,X3] : (k6_relat_1(X2) = k7_relat_1(k6_relat_1(X3),X2) | ~r1_tarski(k2_relat_1(k6_relat_1(X2)),X3)) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f149,f58])).
% 10.89/1.77  fof(f149,plain,(
% 10.89/1.77    ( ! [X2,X3] : (k6_relat_1(X2) = k7_relat_1(k6_relat_1(X3),X2) | ~r1_tarski(k2_relat_1(k6_relat_1(X2)),X3) | ~v1_relat_1(k6_relat_1(X3))) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f138,f58])).
% 10.89/1.77  fof(f138,plain,(
% 10.89/1.77    ( ! [X2,X3] : (k6_relat_1(X2) = k7_relat_1(k6_relat_1(X3),X2) | ~r1_tarski(k2_relat_1(k6_relat_1(X2)),X3) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 10.89/1.77    inference(superposition,[],[f50,f53])).
% 10.89/1.77  fof(f53,plain,(
% 10.89/1.77    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.89/1.77    inference(cnf_transformation,[],[f31])).
% 10.89/1.77  fof(f31,plain,(
% 10.89/1.77    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 10.89/1.77    inference(ennf_transformation,[],[f18])).
% 10.89/1.77  fof(f18,axiom,(
% 10.89/1.77    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 10.89/1.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 10.89/1.77  fof(f50,plain,(
% 10.89/1.77    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 10.89/1.77    inference(cnf_transformation,[],[f29])).
% 10.89/1.77  fof(f29,plain,(
% 10.89/1.77    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 10.89/1.77    inference(flattening,[],[f28])).
% 10.89/1.77  fof(f28,plain,(
% 10.89/1.77    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 10.89/1.77    inference(ennf_transformation,[],[f15])).
% 10.89/1.77  fof(f15,axiom,(
% 10.89/1.77    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 10.89/1.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 10.89/1.77  fof(f131,plain,(
% 10.89/1.77    ( ! [X8,X9] : (v1_relat_1(k1_relat_1(k7_relat_1(X8,X9))) | ~v1_relat_1(k1_relat_1(X8)) | ~v1_relat_1(X8)) )),
% 10.89/1.77    inference(superposition,[],[f47,f46])).
% 10.89/1.77  fof(f47,plain,(
% 10.89/1.77    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 10.89/1.77    inference(cnf_transformation,[],[f25])).
% 10.89/1.77  fof(f25,plain,(
% 10.89/1.77    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 10.89/1.77    inference(ennf_transformation,[],[f10])).
% 10.89/1.77  fof(f10,axiom,(
% 10.89/1.77    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 10.89/1.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 10.89/1.77  fof(f474,plain,(
% 10.89/1.77    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k5_relat_1(X3,k6_relat_1(X4)),X2),k5_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X3) | ~v1_relat_1(k5_relat_1(X3,k6_relat_1(X4)))) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f448,f58])).
% 10.89/1.77  fof(f448,plain,(
% 10.89/1.77    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(k5_relat_1(X3,k6_relat_1(X4)),X2),k5_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X3) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k5_relat_1(X3,k6_relat_1(X4)))) )),
% 10.89/1.77    inference(superposition,[],[f195,f53])).
% 10.89/1.77  fof(f195,plain,(
% 10.89/1.77    ( ! [X6,X8,X7] : (r1_tarski(k5_relat_1(X6,k5_relat_1(X7,k6_relat_1(X8))),k5_relat_1(X6,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X6)) )),
% 10.89/1.77    inference(subsumption_resolution,[],[f194,f49])).
% 10.89/1.78  fof(f49,plain,(
% 10.89/1.78    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.89/1.78    inference(cnf_transformation,[],[f27])).
% 10.89/1.78  fof(f27,plain,(
% 10.89/1.78    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 10.89/1.78    inference(flattening,[],[f26])).
% 10.89/1.78  fof(f26,plain,(
% 10.89/1.78    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 10.89/1.78    inference(ennf_transformation,[],[f8])).
% 10.89/1.78  fof(f8,axiom,(
% 10.89/1.78    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 10.89/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 10.89/1.78  fof(f194,plain,(
% 10.89/1.78    ( ! [X6,X8,X7] : (r1_tarski(k5_relat_1(X6,k5_relat_1(X7,k6_relat_1(X8))),k5_relat_1(X6,X7)) | ~v1_relat_1(k5_relat_1(X6,X7)) | ~v1_relat_1(X7) | ~v1_relat_1(X6)) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f172,f58])).
% 10.89/1.78  fof(f172,plain,(
% 10.89/1.78    ( ! [X6,X8,X7] : (r1_tarski(k5_relat_1(X6,k5_relat_1(X7,k6_relat_1(X8))),k5_relat_1(X6,X7)) | ~v1_relat_1(k5_relat_1(X6,X7)) | ~v1_relat_1(k6_relat_1(X8)) | ~v1_relat_1(X7) | ~v1_relat_1(X6)) )),
% 10.89/1.78    inference(superposition,[],[f51,f45])).
% 10.89/1.78  fof(f45,plain,(
% 10.89/1.78    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.89/1.78    inference(cnf_transformation,[],[f23])).
% 10.89/1.78  fof(f23,plain,(
% 10.89/1.78    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.89/1.78    inference(ennf_transformation,[],[f11])).
% 10.89/1.78  fof(f11,axiom,(
% 10.89/1.78    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 10.89/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 10.89/1.78  fof(f5969,plain,(
% 10.89/1.78    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)) | ~r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)))) )),
% 10.89/1.78    inference(resolution,[],[f1818,f43])).
% 10.89/1.78  fof(f43,plain,(
% 10.89/1.78    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 10.89/1.78    inference(cnf_transformation,[],[f39])).
% 10.89/1.78  fof(f39,plain,(
% 10.89/1.78    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.89/1.78    inference(flattening,[],[f38])).
% 10.89/1.78  fof(f38,plain,(
% 10.89/1.78    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.89/1.78    inference(nnf_transformation,[],[f2])).
% 10.89/1.78  fof(f2,axiom,(
% 10.89/1.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.89/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 10.89/1.78  fof(f1818,plain,(
% 10.89/1.78    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)),k7_relat_1(k6_relat_1(X0),X1))) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f1790,f58])).
% 10.89/1.78  fof(f1790,plain,(
% 10.89/1.78    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 10.89/1.78    inference(superposition,[],[f480,f81])).
% 10.89/1.78  fof(f480,plain,(
% 10.89/1.78    ( ! [X6,X4,X5] : (r1_tarski(k5_relat_1(k6_relat_1(X4),k5_relat_1(X5,k6_relat_1(X6))),k7_relat_1(X5,X4)) | ~v1_relat_1(X5)) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f459,f58])).
% 10.89/1.78  fof(f459,plain,(
% 10.89/1.78    ( ! [X6,X4,X5] : (r1_tarski(k5_relat_1(k6_relat_1(X4),k5_relat_1(X5,k6_relat_1(X6))),k7_relat_1(X5,X4)) | ~v1_relat_1(X5) | ~v1_relat_1(k6_relat_1(X4))) )),
% 10.89/1.78    inference(duplicate_literal_removal,[],[f452])).
% 10.89/1.78  fof(f452,plain,(
% 10.89/1.78    ( ! [X6,X4,X5] : (r1_tarski(k5_relat_1(k6_relat_1(X4),k5_relat_1(X5,k6_relat_1(X6))),k7_relat_1(X5,X4)) | ~v1_relat_1(X5) | ~v1_relat_1(k6_relat_1(X4)) | ~v1_relat_1(X5)) )),
% 10.89/1.78    inference(superposition,[],[f195,f53])).
% 10.89/1.78  fof(f25470,plain,(
% 10.89/1.78    ( ! [X30,X29] : (~r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))),X30) | k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k3_xboole_0(X30,X29))) )),
% 10.89/1.78    inference(forward_demodulation,[],[f25469,f57])).
% 10.89/1.78  fof(f25469,plain,(
% 10.89/1.78    ( ! [X30,X29] : (k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k3_xboole_0(X30,X29)) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))),X30)) )),
% 10.89/1.78    inference(forward_demodulation,[],[f25468,f133])).
% 10.89/1.78  fof(f25468,plain,(
% 10.89/1.78    ( ! [X30,X29] : (k7_relat_1(k6_relat_1(X30),X29) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X30),X29))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))),X30)) )),
% 10.89/1.78    inference(forward_demodulation,[],[f25467,f5985])).
% 10.89/1.78  fof(f25467,plain,(
% 10.89/1.78    ( ! [X30,X29] : (k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))),X30)) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f25466,f58])).
% 10.89/1.78  fof(f25466,plain,(
% 10.89/1.78    ( ! [X30,X29] : (k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))),X30) | ~v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)))))) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f25099,f58])).
% 10.89/1.78  fof(f25099,plain,(
% 10.89/1.78    ( ! [X30,X29] : (k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)))) | ~v1_relat_1(k6_relat_1(X30)) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30))))),X30) | ~v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X29),k6_relat_1(X30)))))) )),
% 10.89/1.78    inference(superposition,[],[f25042,f50])).
% 10.89/1.78  fof(f25042,plain,(
% 10.89/1.78    ( ! [X6,X5] : (k5_relat_1(k6_relat_1(X5),X6) = k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))),X6) | ~v1_relat_1(X6)) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f849,f1881])).
% 10.89/1.78  fof(f1881,plain,(
% 10.89/1.78    ( ! [X10,X11] : (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X10),X11)),X10) | ~v1_relat_1(X11)) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f1864,f317])).
% 10.89/1.78  fof(f317,plain,(
% 10.89/1.78    ( ! [X10,X9] : (v1_relat_1(k5_relat_1(k6_relat_1(X9),X10)) | ~v1_relat_1(X10)) )),
% 10.89/1.78    inference(duplicate_literal_removal,[],[f312])).
% 10.89/1.78  fof(f312,plain,(
% 10.89/1.78    ( ! [X10,X9] : (v1_relat_1(k5_relat_1(k6_relat_1(X9),X10)) | ~v1_relat_1(X10) | ~v1_relat_1(X10)) )),
% 10.89/1.78    inference(resolution,[],[f298,f52])).
% 10.89/1.78  fof(f52,plain,(
% 10.89/1.78    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 10.89/1.78    inference(cnf_transformation,[],[f30])).
% 10.89/1.78  fof(f1864,plain,(
% 10.89/1.78    ( ! [X10,X11] : (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X10),X11)),X10) | ~v1_relat_1(k5_relat_1(k6_relat_1(X10),X11)) | ~v1_relat_1(X11)) )),
% 10.89/1.78    inference(superposition,[],[f128,f567])).
% 10.89/1.78  fof(f567,plain,(
% 10.89/1.78    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(X1)) )),
% 10.89/1.78    inference(forward_demodulation,[],[f566,f57])).
% 10.89/1.78  fof(f566,plain,(
% 10.89/1.78    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1),X0) | ~v1_relat_1(X1)) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f565,f317])).
% 10.89/1.78  fof(f565,plain,(
% 10.89/1.78    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1),X0) | ~v1_relat_1(X1) | ~v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1))) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f535,f58])).
% 10.89/1.78  fof(f535,plain,(
% 10.89/1.78    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1),X0) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X1))) )),
% 10.89/1.78    inference(superposition,[],[f184,f53])).
% 10.89/1.78  fof(f184,plain,(
% 10.89/1.78    ( ! [X8,X7] : (k5_relat_1(X7,k5_relat_1(k6_relat_1(k2_relat_1(X7)),X8)) = k5_relat_1(X7,X8) | ~v1_relat_1(X8) | ~v1_relat_1(X7)) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f177,f58])).
% 10.89/1.78  fof(f177,plain,(
% 10.89/1.78    ( ! [X8,X7] : (k5_relat_1(X7,k5_relat_1(k6_relat_1(k2_relat_1(X7)),X8)) = k5_relat_1(X7,X8) | ~v1_relat_1(X8) | ~v1_relat_1(k6_relat_1(k2_relat_1(X7))) | ~v1_relat_1(X7)) )),
% 10.89/1.78    inference(duplicate_literal_removal,[],[f165])).
% 10.89/1.78  fof(f165,plain,(
% 10.89/1.78    ( ! [X8,X7] : (k5_relat_1(X7,k5_relat_1(k6_relat_1(k2_relat_1(X7)),X8)) = k5_relat_1(X7,X8) | ~v1_relat_1(X8) | ~v1_relat_1(k6_relat_1(k2_relat_1(X7))) | ~v1_relat_1(X7) | ~v1_relat_1(X7)) )),
% 10.89/1.78    inference(superposition,[],[f45,f55])).
% 10.89/1.78  fof(f55,plain,(
% 10.89/1.78    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 10.89/1.78    inference(cnf_transformation,[],[f33])).
% 10.89/1.78  fof(f33,plain,(
% 10.89/1.78    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 10.89/1.78    inference(ennf_transformation,[],[f16])).
% 10.89/1.78  fof(f16,axiom,(
% 10.89/1.78    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 10.89/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 10.89/1.78  fof(f128,plain,(
% 10.89/1.78    ( ! [X2,X3] : (r1_tarski(k1_relat_1(k7_relat_1(X2,X3)),X3) | ~v1_relat_1(X2)) )),
% 10.89/1.78    inference(superposition,[],[f63,f46])).
% 10.89/1.78  fof(f63,plain,(
% 10.89/1.78    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) )),
% 10.89/1.78    inference(superposition,[],[f48,f44])).
% 10.89/1.78  fof(f44,plain,(
% 10.89/1.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 10.89/1.78    inference(cnf_transformation,[],[f1])).
% 10.89/1.78  fof(f1,axiom,(
% 10.89/1.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 10.89/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 10.89/1.78  fof(f849,plain,(
% 10.89/1.78    ( ! [X6,X5] : (~r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6)),X5) | k5_relat_1(k6_relat_1(X5),X6) = k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))),X6) | ~v1_relat_1(X6)) )),
% 10.89/1.78    inference(forward_demodulation,[],[f848,f57])).
% 10.89/1.78  fof(f848,plain,(
% 10.89/1.78    ( ! [X6,X5] : (k5_relat_1(k6_relat_1(X5),X6) = k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))),X6) | ~v1_relat_1(X6) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6)))),X5)) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f847,f317])).
% 10.89/1.78  fof(f847,plain,(
% 10.89/1.78    ( ! [X6,X5] : (k5_relat_1(k6_relat_1(X5),X6) = k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))),X6) | ~v1_relat_1(X6) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6)))),X5) | ~v1_relat_1(k5_relat_1(k6_relat_1(X5),X6))) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f790,f58])).
% 10.89/1.78  fof(f790,plain,(
% 10.89/1.78    ( ! [X6,X5] : (k5_relat_1(k6_relat_1(X5),X6) = k5_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6))),X6) | ~v1_relat_1(X6) | ~v1_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6)))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X5),X6)))),X5) | ~v1_relat_1(k5_relat_1(k6_relat_1(X5),X6))) )),
% 10.89/1.78    inference(superposition,[],[f185,f54])).
% 10.89/1.78  fof(f185,plain,(
% 10.89/1.78    ( ! [X10,X11,X9] : (k5_relat_1(X9,k5_relat_1(k6_relat_1(X10),X11)) = k5_relat_1(X9,X11) | ~v1_relat_1(X11) | ~v1_relat_1(X9) | ~r1_tarski(k2_relat_1(X9),X10)) )),
% 10.89/1.78    inference(subsumption_resolution,[],[f176,f58])).
% 10.89/1.78  fof(f176,plain,(
% 10.89/1.78    ( ! [X10,X11,X9] : (k5_relat_1(X9,k5_relat_1(k6_relat_1(X10),X11)) = k5_relat_1(X9,X11) | ~v1_relat_1(X11) | ~v1_relat_1(k6_relat_1(X10)) | ~v1_relat_1(X9) | ~r1_tarski(k2_relat_1(X9),X10)) )),
% 10.89/1.78    inference(duplicate_literal_removal,[],[f166])).
% 10.89/1.78  fof(f166,plain,(
% 10.89/1.78    ( ! [X10,X11,X9] : (k5_relat_1(X9,k5_relat_1(k6_relat_1(X10),X11)) = k5_relat_1(X9,X11) | ~v1_relat_1(X11) | ~v1_relat_1(k6_relat_1(X10)) | ~v1_relat_1(X9) | ~r1_tarski(k2_relat_1(X9),X10) | ~v1_relat_1(X9)) )),
% 10.89/1.78    inference(superposition,[],[f45,f50])).
% 10.89/1.78  fof(f116,plain,(
% 10.89/1.78    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 10.89/1.78    inference(subsumption_resolution,[],[f101,f58])).
% 10.89/1.78  fof(f101,plain,(
% 10.89/1.78    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 10.89/1.78    inference(superposition,[],[f40,f53])).
% 10.89/1.78  fof(f40,plain,(
% 10.89/1.78    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 10.89/1.78    inference(cnf_transformation,[],[f37])).
% 10.89/1.78  fof(f37,plain,(
% 10.89/1.78    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 10.89/1.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f36])).
% 10.89/1.78  fof(f36,plain,(
% 10.89/1.78    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 10.89/1.78    introduced(choice_axiom,[])).
% 10.89/1.78  fof(f22,plain,(
% 10.89/1.78    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 10.89/1.78    inference(ennf_transformation,[],[f21])).
% 10.89/1.78  fof(f21,negated_conjecture,(
% 10.89/1.78    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 10.89/1.78    inference(negated_conjecture,[],[f20])).
% 10.89/1.78  fof(f20,conjecture,(
% 10.89/1.78    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 10.89/1.78    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 10.89/1.78  % SZS output end Proof for theBenchmark
% 10.89/1.78  % (32297)------------------------------
% 10.89/1.78  % (32297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.89/1.78  % (32297)Termination reason: Refutation
% 10.89/1.78  
% 10.89/1.78  % (32297)Memory used [KB]: 17526
% 10.89/1.78  % (32297)Time elapsed: 1.174 s
% 10.89/1.78  % (32297)------------------------------
% 10.89/1.78  % (32297)------------------------------
% 10.89/1.78  % (32237)Success in time 1.401 s
%------------------------------------------------------------------------------
