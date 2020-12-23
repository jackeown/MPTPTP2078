%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:28 EST 2020

% Result     : Theorem 14.61s
% Output     : Refutation 14.61s
% Verified   : 
% Statistics : Number of formulae       :  162 (25674 expanded)
%              Number of leaves         :   17 (7789 expanded)
%              Depth                    :   37
%              Number of atoms          :  217 (33964 expanded)
%              Number of equality atoms :  129 (21264 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32708,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f32707])).

fof(f32707,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f30606,f31728])).

fof(f31728,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3) ),
    inference(superposition,[],[f27406,f31112])).

fof(f31112,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X3) ),
    inference(forward_demodulation,[],[f31111,f1318])).

fof(f1318,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(forward_demodulation,[],[f1310,f66])).

fof(f66,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f42,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1310,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(superposition,[],[f1306,f69])).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f66,f62])).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f60,f32])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0)) ),
    inference(resolution,[],[f34,f31])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1306,plain,(
    ! [X4,X5,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X5),X4),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X5)) ),
    inference(forward_demodulation,[],[f1305,f66])).

fof(f1305,plain,(
    ! [X4,X5,X3] : k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)),k6_relat_1(X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X4),X3) ),
    inference(forward_demodulation,[],[f1301,f285])).

fof(f285,plain,(
    ! [X6,X7,X5] : k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5) ),
    inference(resolution,[],[f279,f42])).

fof(f279,plain,(
    ! [X6,X7] : v1_relat_1(k7_relat_1(k6_relat_1(X6),X7)) ),
    inference(forward_demodulation,[],[f278,f32])).

fof(f278,plain,(
    ! [X6,X7] : v1_relat_1(k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X6),X7)))) ),
    inference(subsumption_resolution,[],[f274,f31])).

fof(f274,plain,(
    ! [X6,X7] :
      ( v1_relat_1(k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X6),X7))))
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(superposition,[],[f161,f84])).

fof(f84,plain,(
    ! [X8,X7] : k6_relat_1(k7_relat_1(k6_relat_1(X7),X8)) = k7_relat_1(k6_relat_1(k6_relat_1(X7)),k7_relat_1(k6_relat_1(X7),X8)) ),
    inference(resolution,[],[f79,f73])).

fof(f73,plain,(
    ! [X2,X1] : r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2)) ),
    inference(subsumption_resolution,[],[f71,f31])).

fof(f71,plain,(
    ! [X2,X1] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f45,f66])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f78,f66])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f77,f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f46,f33])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f161,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f58,f158])).

fof(f158,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f154,f32])).

fof(f154,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f59,f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(forward_demodulation,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f54,f53])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1301,plain,(
    ! [X4,X5,X3] : k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)),k6_relat_1(X5)) = k5_relat_1(k6_relat_1(X3),k7_relat_1(k6_relat_1(X5),X4)) ),
    inference(resolution,[],[f654,f31])).

fof(f654,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),k6_relat_1(X5)) = k5_relat_1(X3,k7_relat_1(k6_relat_1(X5),X4)) ) ),
    inference(forward_demodulation,[],[f650,f66])).

fof(f650,plain,(
    ! [X4,X5,X3] :
      ( k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),k6_relat_1(X5)) = k5_relat_1(X3,k5_relat_1(k6_relat_1(X4),k6_relat_1(X5)))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f300,f31])).

fof(f300,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(X4)
      | k5_relat_1(k5_relat_1(X3,X4),k6_relat_1(X5)) = k5_relat_1(X3,k5_relat_1(X4,k6_relat_1(X5)))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f35,f31])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f31111,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X2),X3) ),
    inference(forward_demodulation,[],[f31087,f27386])).

fof(f27386,plain,(
    ! [X532,X533] : k7_relat_1(k6_relat_1(X532),X533) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X532),X533))) ),
    inference(forward_demodulation,[],[f26661,f32])).

fof(f26661,plain,(
    ! [X532,X533] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X532),X533))) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X532),X533))) ),
    inference(superposition,[],[f32,f25620])).

fof(f25620,plain,(
    ! [X0,X1] : k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k6_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(backward_demodulation,[],[f2624,f25619])).

fof(f25619,plain,(
    ! [X331,X330] : k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))) ),
    inference(forward_demodulation,[],[f25618,f69])).

fof(f25618,plain,(
    ! [X331,X330] : k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k7_relat_1(k6_relat_1(X330),X331)) ),
    inference(forward_demodulation,[],[f25617,f25605])).

fof(f25605,plain,(
    ! [X300,X301,X299] : k7_relat_1(k7_relat_1(k6_relat_1(X301),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X299),X300)))),k7_relat_1(k6_relat_1(X299),X300)) = k7_relat_1(k6_relat_1(X301),k7_relat_1(k6_relat_1(X299),X300)) ),
    inference(forward_demodulation,[],[f25241,f66])).

fof(f25241,plain,(
    ! [X300,X301,X299] : k7_relat_1(k7_relat_1(k6_relat_1(X301),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X299),X300)))),k7_relat_1(k6_relat_1(X299),X300)) = k5_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X299),X300)),k6_relat_1(X301)) ),
    inference(superposition,[],[f1306,f1748])).

fof(f1748,plain,(
    ! [X0,X1] : k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f1650,f79])).

fof(f1650,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(forward_demodulation,[],[f1602,f171])).

fof(f171,plain,(
    ! [X0,X1] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(backward_demodulation,[],[f104,f158])).

fof(f104,plain,(
    ! [X0,X1] : k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(resolution,[],[f101,f79])).

fof(f101,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(forward_demodulation,[],[f94,f53])).

fof(f94,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k2_enumset1(X3,X3,X3,X2)),X2) ),
    inference(superposition,[],[f57,f86])).

fof(f86,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4)) ),
    inference(superposition,[],[f52,f53])).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f37,f49,f49])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f51,f53])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1602,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(superposition,[],[f1325,f1576])).

fof(f1576,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(superposition,[],[f286,f285])).

fof(f286,plain,(
    ! [X8,X9] : k7_relat_1(k6_relat_1(X8),X9) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X8),X9))),k7_relat_1(k6_relat_1(X8),X9)) ),
    inference(resolution,[],[f279,f34])).

fof(f1325,plain,(
    ! [X2,X0,X1] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f1317,f279])).

fof(f1317,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(superposition,[],[f44,f1306])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25617,plain,(
    ! [X331,X330] : k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))) = k7_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))),k7_relat_1(k6_relat_1(X330),X331)) ),
    inference(forward_demodulation,[],[f25254,f32])).

fof(f25254,plain,(
    ! [X331,X330] : k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))) = k7_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))),k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)))) ),
    inference(superposition,[],[f1593,f1748])).

fof(f1593,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[],[f1576,f225])).

fof(f225,plain,(
    ! [X2,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f166,f158])).

fof(f166,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X6)) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7)) ),
    inference(backward_demodulation,[],[f92,f158])).

fof(f92,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f86,f53])).

fof(f2624,plain,(
    ! [X0,X1] : k6_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(resolution,[],[f2591,f79])).

fof(f2591,plain,(
    ! [X0,X1] : r1_tarski(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f2541,f1623])).

fof(f1623,plain,(
    ! [X6,X7] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),X7) ),
    inference(forward_demodulation,[],[f1597,f1436])).

fof(f1436,plain,(
    ! [X4,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))),X4),k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) ),
    inference(forward_demodulation,[],[f1422,f33])).

fof(f1422,plain,(
    ! [X4,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))))),X4),k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) ),
    inference(superposition,[],[f1409,f171])).

fof(f1409,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3) ),
    inference(superposition,[],[f284,f1306])).

fof(f284,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)))) ),
    inference(resolution,[],[f279,f193])).

fof(f193,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(resolution,[],[f192,f46])).

fof(f192,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f191,f32])).

fof(f191,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k6_relat_1(X0)),X0) ),
    inference(superposition,[],[f160,f69])).

fof(f160,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(backward_demodulation,[],[f57,f158])).

fof(f1597,plain,(
    ! [X6,X7] : k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),X7) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),X7),k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))) ),
    inference(superposition,[],[f1576,f1075])).

fof(f1075,plain,(
    ! [X4,X5] : k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))),X4)) ),
    inference(forward_demodulation,[],[f1034,f32])).

fof(f1034,plain,(
    ! [X4,X5] : k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)))) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))))),X4)) ),
    inference(superposition,[],[f640,f171])).

fof(f640,plain,(
    ! [X2,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)) ),
    inference(forward_demodulation,[],[f639,f32])).

fof(f639,plain,(
    ! [X2,X3] : k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)) ),
    inference(forward_demodulation,[],[f628,f32])).

fof(f628,plain,(
    ! [X2,X3] : k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)) = k1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))))) ),
    inference(superposition,[],[f625,f164])).

fof(f164,plain,(
    ! [X0,X1] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(backward_demodulation,[],[f80,f158])).

fof(f80,plain,(
    ! [X0,X1] : k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(resolution,[],[f79,f57])).

fof(f625,plain,(
    ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X3)))) ),
    inference(forward_demodulation,[],[f624,f171])).

fof(f624,plain,(
    ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X4),X3)))) ),
    inference(forward_demodulation,[],[f614,f546])).

fof(f546,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f545,f32])).

fof(f545,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)))) = k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(forward_demodulation,[],[f544,f164])).

fof(f544,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) ),
    inference(forward_demodulation,[],[f531,f225])).

fof(f531,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0)) = k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f166,f222])).

fof(f222,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[],[f158,f158])).

fof(f614,plain,(
    ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X4),X3)))) = k4_xboole_0(X3,k1_relat_1(k7_relat_1(k6_relat_1(X3),k4_xboole_0(X3,X4)))) ),
    inference(superposition,[],[f158,f242])).

fof(f242,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f223,f241])).

fof(f241,plain,(
    ! [X2,X3] : k1_relat_1(k7_relat_1(k6_relat_1(k4_xboole_0(X2,X3)),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),k4_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f224,f222])).

fof(f224,plain,(
    ! [X2,X3] : k1_relat_1(k7_relat_1(k6_relat_1(k4_xboole_0(X2,X3)),X2)) = k4_xboole_0(X2,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(superposition,[],[f166,f158])).

fof(f223,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k1_relat_1(k7_relat_1(k6_relat_1(k4_xboole_0(X0,X1)),X0)) ),
    inference(superposition,[],[f166,f166])).

fof(f2541,plain,(
    ! [X2,X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))),X2),k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(superposition,[],[f2445,f225])).

fof(f2445,plain,(
    ! [X101,X102,X100] : r1_tarski(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X100),X101))),X102),k7_relat_1(k6_relat_1(X101),X102)) ),
    inference(superposition,[],[f1325,f1623])).

fof(f31087,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X2))),X2),X3) ),
    inference(backward_demodulation,[],[f1409,f30609])).

fof(f30609,plain,(
    ! [X4,X5] : k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) = k2_relat_1(k7_relat_1(k6_relat_1(X5),X4)) ),
    inference(superposition,[],[f33,f27965])).

fof(f27965,plain,(
    ! [X4,X5] : k7_relat_1(k6_relat_1(X4),X5) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) ),
    inference(forward_demodulation,[],[f27399,f1593])).

fof(f27399,plain,(
    ! [X4,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) ),
    inference(backward_demodulation,[],[f836,f27386])).

fof(f836,plain,(
    ! [X4,X5] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))),k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) ),
    inference(superposition,[],[f164,f623])).

fof(f623,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),X1)) ),
    inference(forward_demodulation,[],[f613,f546])).

fof(f613,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),X1)) = k4_xboole_0(X1,k1_relat_1(k7_relat_1(k6_relat_1(X1),k4_xboole_0(X1,X2)))) ),
    inference(superposition,[],[f166,f242])).

fof(f27406,plain,(
    ! [X10,X11] : k7_relat_1(k6_relat_1(X10),X11) = k7_relat_1(k7_relat_1(k6_relat_1(X10),X11),X10) ),
    inference(backward_demodulation,[],[f1632,f27386])).

fof(f1632,plain,(
    ! [X10,X11] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X10),X11))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X10),X11))),X10) ),
    inference(forward_demodulation,[],[f1599,f1435])).

fof(f1435,plain,(
    ! [X2,X3] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(forward_demodulation,[],[f1421,f33])).

fof(f1421,plain,(
    ! [X2,X3] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))))),X2),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(superposition,[],[f1409,f164])).

fof(f1599,plain,(
    ! [X10,X11] : k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X10),X11))),X10) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X10),X11))),X10),k1_relat_1(k7_relat_1(k6_relat_1(X10),X11))) ),
    inference(superposition,[],[f1576,f640])).

fof(f30606,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(superposition,[],[f182,f27965])).

fof(f182,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f68,f158])).

fof(f68,plain,(
    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f56,f66])).

fof(f56,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f50,f53])).

fof(f50,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f30,f49])).

fof(f30,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f28])).

fof(f28,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (8292)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.44  % (8289)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (8290)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (8281)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (8287)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (8291)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (8280)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (8282)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (8279)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (8278)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (8277)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (8293)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (8288)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (8288)Refutation not found, incomplete strategy% (8288)------------------------------
% 0.20/0.49  % (8288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8288)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8288)Memory used [KB]: 10618
% 0.20/0.49  % (8288)Time elapsed: 0.082 s
% 0.20/0.49  % (8288)------------------------------
% 0.20/0.49  % (8288)------------------------------
% 0.20/0.49  % (8286)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (8284)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (8283)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (8276)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.26/0.52  % (8294)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.12/1.02  % (8280)Time limit reached!
% 5.12/1.02  % (8280)------------------------------
% 5.12/1.02  % (8280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.12/1.02  % (8280)Termination reason: Time limit
% 5.12/1.02  % (8280)Termination phase: Saturation
% 5.12/1.02  
% 5.12/1.02  % (8280)Memory used [KB]: 17654
% 5.12/1.02  % (8280)Time elapsed: 0.600 s
% 5.12/1.02  % (8280)------------------------------
% 5.12/1.02  % (8280)------------------------------
% 12.16/1.92  % (8281)Time limit reached!
% 12.16/1.92  % (8281)------------------------------
% 12.16/1.92  % (8281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.16/1.93  % (8281)Termination reason: Time limit
% 12.16/1.93  % (8281)Termination phase: Saturation
% 12.16/1.93  
% 12.16/1.93  % (8281)Memory used [KB]: 34285
% 12.16/1.93  % (8281)Time elapsed: 1.500 s
% 12.16/1.93  % (8281)------------------------------
% 12.16/1.93  % (8281)------------------------------
% 12.96/2.02  % (8282)Time limit reached!
% 12.96/2.02  % (8282)------------------------------
% 12.96/2.02  % (8282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.96/2.02  % (8282)Termination reason: Time limit
% 12.96/2.02  
% 12.96/2.02  % (8282)Memory used [KB]: 28656
% 12.96/2.02  % (8282)Time elapsed: 1.543 s
% 12.96/2.02  % (8282)------------------------------
% 12.96/2.02  % (8282)------------------------------
% 14.61/2.22  % (8278)Time limit reached!
% 14.61/2.22  % (8278)------------------------------
% 14.61/2.22  % (8278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.61/2.22  % (8278)Termination reason: Time limit
% 14.61/2.22  % (8278)Termination phase: Saturation
% 14.61/2.22  
% 14.61/2.22  % (8278)Memory used [KB]: 40041
% 14.61/2.22  % (8278)Time elapsed: 1.800 s
% 14.61/2.22  % (8278)------------------------------
% 14.61/2.22  % (8278)------------------------------
% 14.61/2.22  % (8286)Refutation found. Thanks to Tanya!
% 14.61/2.22  % SZS status Theorem for theBenchmark
% 14.61/2.22  % SZS output start Proof for theBenchmark
% 14.61/2.22  fof(f32708,plain,(
% 14.61/2.22    $false),
% 14.61/2.22    inference(trivial_inequality_removal,[],[f32707])).
% 14.61/2.22  fof(f32707,plain,(
% 14.61/2.22    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 14.61/2.22    inference(superposition,[],[f30606,f31728])).
% 14.61/2.22  fof(f31728,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)) )),
% 14.61/2.22    inference(superposition,[],[f27406,f31112])).
% 14.61/2.22  fof(f31112,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X3)) )),
% 14.61/2.22    inference(forward_demodulation,[],[f31111,f1318])).
% 14.61/2.22  fof(f1318,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) )),
% 14.61/2.22    inference(forward_demodulation,[],[f1310,f66])).
% 14.61/2.22  fof(f66,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 14.61/2.22    inference(resolution,[],[f42,f31])).
% 14.61/2.22  fof(f31,plain,(
% 14.61/2.22    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 14.61/2.22    inference(cnf_transformation,[],[f18])).
% 14.61/2.22  fof(f18,plain,(
% 14.61/2.22    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 14.61/2.22    inference(pure_predicate_removal,[],[f15])).
% 14.61/2.22  fof(f15,axiom,(
% 14.61/2.22    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 14.61/2.22  fof(f42,plain,(
% 14.61/2.22    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f23])).
% 14.61/2.22  fof(f23,plain,(
% 14.61/2.22    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 14.61/2.22    inference(ennf_transformation,[],[f14])).
% 14.61/2.22  fof(f14,axiom,(
% 14.61/2.22    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 14.61/2.22  fof(f1310,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) )),
% 14.61/2.22    inference(superposition,[],[f1306,f69])).
% 14.61/2.22  fof(f69,plain,(
% 14.61/2.22    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 14.61/2.22    inference(superposition,[],[f66,f62])).
% 14.61/2.22  fof(f62,plain,(
% 14.61/2.22    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f60,f32])).
% 14.61/2.22  fof(f32,plain,(
% 14.61/2.22    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 14.61/2.22    inference(cnf_transformation,[],[f9])).
% 14.61/2.22  fof(f9,axiom,(
% 14.61/2.22    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 14.61/2.22  fof(f60,plain,(
% 14.61/2.22    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k6_relat_1(X0))) )),
% 14.61/2.22    inference(resolution,[],[f34,f31])).
% 14.61/2.22  fof(f34,plain,(
% 14.61/2.22    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 14.61/2.22    inference(cnf_transformation,[],[f20])).
% 14.61/2.22  fof(f20,plain,(
% 14.61/2.22    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 14.61/2.22    inference(ennf_transformation,[],[f11])).
% 14.61/2.22  fof(f11,axiom,(
% 14.61/2.22    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 14.61/2.22  fof(f1306,plain,(
% 14.61/2.22    ( ! [X4,X5,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X5),X4),X3) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X5))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f1305,f66])).
% 14.61/2.22  fof(f1305,plain,(
% 14.61/2.22    ( ! [X4,X5,X3] : (k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)),k6_relat_1(X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X4),X3)) )),
% 14.61/2.22    inference(forward_demodulation,[],[f1301,f285])).
% 14.61/2.22  fof(f285,plain,(
% 14.61/2.22    ( ! [X6,X7,X5] : (k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) )),
% 14.61/2.22    inference(resolution,[],[f279,f42])).
% 14.61/2.22  fof(f279,plain,(
% 14.61/2.22    ( ! [X6,X7] : (v1_relat_1(k7_relat_1(k6_relat_1(X6),X7))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f278,f32])).
% 14.61/2.22  fof(f278,plain,(
% 14.61/2.22    ( ! [X6,X7] : (v1_relat_1(k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X6),X7))))) )),
% 14.61/2.22    inference(subsumption_resolution,[],[f274,f31])).
% 14.61/2.22  fof(f274,plain,(
% 14.61/2.22    ( ! [X6,X7] : (v1_relat_1(k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X6),X7)))) | ~v1_relat_1(k6_relat_1(X6))) )),
% 14.61/2.22    inference(superposition,[],[f161,f84])).
% 14.61/2.22  fof(f84,plain,(
% 14.61/2.22    ( ! [X8,X7] : (k6_relat_1(k7_relat_1(k6_relat_1(X7),X8)) = k7_relat_1(k6_relat_1(k6_relat_1(X7)),k7_relat_1(k6_relat_1(X7),X8))) )),
% 14.61/2.22    inference(resolution,[],[f79,f73])).
% 14.61/2.22  fof(f73,plain,(
% 14.61/2.22    ( ! [X2,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2))) )),
% 14.61/2.22    inference(subsumption_resolution,[],[f71,f31])).
% 14.61/2.22  fof(f71,plain,(
% 14.61/2.22    ( ! [X2,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 14.61/2.22    inference(superposition,[],[f45,f66])).
% 14.61/2.22  fof(f45,plain,(
% 14.61/2.22    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f25])).
% 14.61/2.22  fof(f25,plain,(
% 14.61/2.22    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 14.61/2.22    inference(ennf_transformation,[],[f10])).
% 14.61/2.22  fof(f10,axiom,(
% 14.61/2.22    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 14.61/2.22  fof(f79,plain,(
% 14.61/2.22    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 14.61/2.22    inference(forward_demodulation,[],[f78,f66])).
% 14.61/2.22  fof(f78,plain,(
% 14.61/2.22    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 14.61/2.22    inference(subsumption_resolution,[],[f77,f31])).
% 14.61/2.22  fof(f77,plain,(
% 14.61/2.22    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 14.61/2.22    inference(superposition,[],[f46,f33])).
% 14.61/2.22  fof(f33,plain,(
% 14.61/2.22    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 14.61/2.22    inference(cnf_transformation,[],[f9])).
% 14.61/2.22  fof(f46,plain,(
% 14.61/2.22    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f27])).
% 14.61/2.22  fof(f27,plain,(
% 14.61/2.22    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 14.61/2.22    inference(flattening,[],[f26])).
% 14.61/2.22  fof(f26,plain,(
% 14.61/2.22    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 14.61/2.22    inference(ennf_transformation,[],[f12])).
% 14.61/2.22  fof(f12,axiom,(
% 14.61/2.22    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 14.61/2.22  fof(f161,plain,(
% 14.61/2.22    ( ! [X0,X1] : (v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) | ~v1_relat_1(X0)) )),
% 14.61/2.22    inference(backward_demodulation,[],[f58,f158])).
% 14.61/2.22  fof(f158,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f154,f32])).
% 14.61/2.22  fof(f154,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 14.61/2.22    inference(resolution,[],[f59,f31])).
% 14.61/2.22  fof(f59,plain,(
% 14.61/2.22    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f55,f53])).
% 14.61/2.22  fof(f53,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 14.61/2.22    inference(definition_unfolding,[],[f40,f49])).
% 14.61/2.22  fof(f49,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 14.61/2.22    inference(definition_unfolding,[],[f38,f48])).
% 14.61/2.22  fof(f48,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 14.61/2.22    inference(definition_unfolding,[],[f39,f47])).
% 14.61/2.22  fof(f47,plain,(
% 14.61/2.22    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f5])).
% 14.61/2.22  fof(f5,axiom,(
% 14.61/2.22    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 14.61/2.22  fof(f39,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f4])).
% 14.61/2.22  fof(f4,axiom,(
% 14.61/2.22    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 14.61/2.22  fof(f38,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 14.61/2.22    inference(cnf_transformation,[],[f6])).
% 14.61/2.22  fof(f6,axiom,(
% 14.61/2.22    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 14.61/2.22  fof(f40,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 14.61/2.22    inference(cnf_transformation,[],[f3])).
% 14.61/2.22  fof(f3,axiom,(
% 14.61/2.22    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 14.61/2.22  fof(f55,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 14.61/2.22    inference(definition_unfolding,[],[f43,f49])).
% 14.61/2.22  fof(f43,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f24])).
% 14.61/2.22  fof(f24,plain,(
% 14.61/2.22    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 14.61/2.22    inference(ennf_transformation,[],[f13])).
% 14.61/2.22  fof(f13,axiom,(
% 14.61/2.22    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 14.61/2.22  fof(f58,plain,(
% 14.61/2.22    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X0)) )),
% 14.61/2.22    inference(forward_demodulation,[],[f54,f53])).
% 14.61/2.22  fof(f54,plain,(
% 14.61/2.22    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 14.61/2.22    inference(definition_unfolding,[],[f41,f49])).
% 14.61/2.22  fof(f41,plain,(
% 14.61/2.22    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f22])).
% 14.61/2.22  fof(f22,plain,(
% 14.61/2.22    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 14.61/2.22    inference(ennf_transformation,[],[f7])).
% 14.61/2.22  fof(f7,axiom,(
% 14.61/2.22    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 14.61/2.22  fof(f1301,plain,(
% 14.61/2.22    ( ! [X4,X5,X3] : (k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)),k6_relat_1(X5)) = k5_relat_1(k6_relat_1(X3),k7_relat_1(k6_relat_1(X5),X4))) )),
% 14.61/2.22    inference(resolution,[],[f654,f31])).
% 14.61/2.22  fof(f654,plain,(
% 14.61/2.22    ( ! [X4,X5,X3] : (~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),k6_relat_1(X5)) = k5_relat_1(X3,k7_relat_1(k6_relat_1(X5),X4))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f650,f66])).
% 14.61/2.22  fof(f650,plain,(
% 14.61/2.22    ( ! [X4,X5,X3] : (k5_relat_1(k5_relat_1(X3,k6_relat_1(X4)),k6_relat_1(X5)) = k5_relat_1(X3,k5_relat_1(k6_relat_1(X4),k6_relat_1(X5))) | ~v1_relat_1(X3)) )),
% 14.61/2.22    inference(resolution,[],[f300,f31])).
% 14.61/2.22  fof(f300,plain,(
% 14.61/2.22    ( ! [X4,X5,X3] : (~v1_relat_1(X4) | k5_relat_1(k5_relat_1(X3,X4),k6_relat_1(X5)) = k5_relat_1(X3,k5_relat_1(X4,k6_relat_1(X5))) | ~v1_relat_1(X3)) )),
% 14.61/2.22    inference(resolution,[],[f35,f31])).
% 14.61/2.22  fof(f35,plain,(
% 14.61/2.22    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f21])).
% 14.61/2.22  fof(f21,plain,(
% 14.61/2.22    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 14.61/2.22    inference(ennf_transformation,[],[f8])).
% 14.61/2.22  fof(f8,axiom,(
% 14.61/2.22    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 14.61/2.22  fof(f31111,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X2),X2),X3)) )),
% 14.61/2.22    inference(forward_demodulation,[],[f31087,f27386])).
% 14.61/2.22  fof(f27386,plain,(
% 14.61/2.22    ( ! [X532,X533] : (k7_relat_1(k6_relat_1(X532),X533) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X532),X533)))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f26661,f32])).
% 14.61/2.22  fof(f26661,plain,(
% 14.61/2.22    ( ! [X532,X533] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X532),X533))) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X532),X533)))) )),
% 14.61/2.22    inference(superposition,[],[f32,f25620])).
% 14.61/2.22  fof(f25620,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k6_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) )),
% 14.61/2.22    inference(backward_demodulation,[],[f2624,f25619])).
% 14.61/2.22  fof(f25619,plain,(
% 14.61/2.22    ( ! [X331,X330] : (k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331))))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f25618,f69])).
% 14.61/2.22  fof(f25618,plain,(
% 14.61/2.22    ( ! [X331,X330] : (k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k7_relat_1(k6_relat_1(X330),X331))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f25617,f25605])).
% 14.61/2.22  fof(f25605,plain,(
% 14.61/2.22    ( ! [X300,X301,X299] : (k7_relat_1(k7_relat_1(k6_relat_1(X301),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X299),X300)))),k7_relat_1(k6_relat_1(X299),X300)) = k7_relat_1(k6_relat_1(X301),k7_relat_1(k6_relat_1(X299),X300))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f25241,f66])).
% 14.61/2.22  fof(f25241,plain,(
% 14.61/2.22    ( ! [X300,X301,X299] : (k7_relat_1(k7_relat_1(k6_relat_1(X301),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X299),X300)))),k7_relat_1(k6_relat_1(X299),X300)) = k5_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X299),X300)),k6_relat_1(X301))) )),
% 14.61/2.22    inference(superposition,[],[f1306,f1748])).
% 14.61/2.22  fof(f1748,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))),k7_relat_1(k6_relat_1(X0),X1))) )),
% 14.61/2.22    inference(resolution,[],[f1650,f79])).
% 14.61/2.22  fof(f1650,plain,(
% 14.61/2.22    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f1602,f171])).
% 14.61/2.22  fof(f171,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 14.61/2.22    inference(backward_demodulation,[],[f104,f158])).
% 14.61/2.22  fof(f104,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 14.61/2.22    inference(resolution,[],[f101,f79])).
% 14.61/2.22  fof(f101,plain,(
% 14.61/2.22    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 14.61/2.22    inference(forward_demodulation,[],[f94,f53])).
% 14.61/2.22  fof(f94,plain,(
% 14.61/2.22    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k2_enumset1(X3,X3,X3,X2)),X2)) )),
% 14.61/2.22    inference(superposition,[],[f57,f86])).
% 14.61/2.22  fof(f86,plain,(
% 14.61/2.22    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4))) )),
% 14.61/2.22    inference(superposition,[],[f52,f53])).
% 14.61/2.22  fof(f52,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 14.61/2.22    inference(definition_unfolding,[],[f37,f49,f49])).
% 14.61/2.22  fof(f37,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f1])).
% 14.61/2.22  fof(f1,axiom,(
% 14.61/2.22    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 14.61/2.22  fof(f57,plain,(
% 14.61/2.22    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 14.61/2.22    inference(backward_demodulation,[],[f51,f53])).
% 14.61/2.22  fof(f51,plain,(
% 14.61/2.22    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 14.61/2.22    inference(definition_unfolding,[],[f36,f49])).
% 14.61/2.22  fof(f36,plain,(
% 14.61/2.22    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f2])).
% 14.61/2.22  fof(f2,axiom,(
% 14.61/2.22    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 14.61/2.22  fof(f1602,plain,(
% 14.61/2.22    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) )),
% 14.61/2.22    inference(superposition,[],[f1325,f1576])).
% 14.61/2.22  fof(f1576,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) )),
% 14.61/2.22    inference(superposition,[],[f286,f285])).
% 14.61/2.22  fof(f286,plain,(
% 14.61/2.22    ( ! [X8,X9] : (k7_relat_1(k6_relat_1(X8),X9) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X8),X9))),k7_relat_1(k6_relat_1(X8),X9))) )),
% 14.61/2.22    inference(resolution,[],[f279,f34])).
% 14.61/2.22  fof(f1325,plain,(
% 14.61/2.22    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1))) )),
% 14.61/2.22    inference(subsumption_resolution,[],[f1317,f279])).
% 14.61/2.22  fof(f1317,plain,(
% 14.61/2.22    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 14.61/2.22    inference(superposition,[],[f44,f1306])).
% 14.61/2.22  fof(f44,plain,(
% 14.61/2.22    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 14.61/2.22    inference(cnf_transformation,[],[f25])).
% 14.61/2.22  fof(f25617,plain,(
% 14.61/2.22    ( ! [X331,X330] : (k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))) = k7_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))),k7_relat_1(k6_relat_1(X330),X331))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f25254,f32])).
% 14.61/2.22  fof(f25254,plain,(
% 14.61/2.22    ( ! [X331,X330] : (k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))) = k7_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X330),X331)))),k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X330),X331))))) )),
% 14.61/2.22    inference(superposition,[],[f1593,f1748])).
% 14.61/2.22  fof(f1593,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 14.61/2.22    inference(superposition,[],[f1576,f225])).
% 14.61/2.22  fof(f225,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) )),
% 14.61/2.22    inference(superposition,[],[f166,f158])).
% 14.61/2.22  fof(f166,plain,(
% 14.61/2.22    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X6)) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))) )),
% 14.61/2.22    inference(backward_demodulation,[],[f92,f158])).
% 14.61/2.22  fof(f92,plain,(
% 14.61/2.22    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k4_xboole_0(X7,k4_xboole_0(X7,X6))) )),
% 14.61/2.22    inference(superposition,[],[f86,f53])).
% 14.61/2.22  fof(f2624,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k6_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) )),
% 14.61/2.22    inference(resolution,[],[f2591,f79])).
% 14.61/2.22  fof(f2591,plain,(
% 14.61/2.22    ( ! [X0,X1] : (r1_tarski(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),k7_relat_1(k6_relat_1(X0),X1))) )),
% 14.61/2.22    inference(superposition,[],[f2541,f1623])).
% 14.61/2.22  fof(f1623,plain,(
% 14.61/2.22    ( ! [X6,X7] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),X7)) )),
% 14.61/2.22    inference(forward_demodulation,[],[f1597,f1436])).
% 14.61/2.22  fof(f1436,plain,(
% 14.61/2.22    ( ! [X4,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))),X4),k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f1422,f33])).
% 14.61/2.22  fof(f1422,plain,(
% 14.61/2.22    ( ! [X4,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))))),X4),k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)))) )),
% 14.61/2.22    inference(superposition,[],[f1409,f171])).
% 14.61/2.22  fof(f1409,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3)) )),
% 14.61/2.22    inference(superposition,[],[f284,f1306])).
% 14.61/2.22  fof(f284,plain,(
% 14.61/2.22    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))))) )),
% 14.61/2.22    inference(resolution,[],[f279,f193])).
% 14.61/2.22  fof(f193,plain,(
% 14.61/2.22    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 14.61/2.22    inference(resolution,[],[f192,f46])).
% 14.61/2.22  fof(f192,plain,(
% 14.61/2.22    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 14.61/2.22    inference(forward_demodulation,[],[f191,f32])).
% 14.61/2.22  fof(f191,plain,(
% 14.61/2.22    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),X0)) )),
% 14.61/2.22    inference(superposition,[],[f160,f69])).
% 14.61/2.22  fof(f160,plain,(
% 14.61/2.22    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 14.61/2.22    inference(backward_demodulation,[],[f57,f158])).
% 14.61/2.22  fof(f1597,plain,(
% 14.61/2.22    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),X7) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))),X7),k1_relat_1(k7_relat_1(k6_relat_1(X6),X7)))) )),
% 14.61/2.22    inference(superposition,[],[f1576,f1075])).
% 14.61/2.22  fof(f1075,plain,(
% 14.61/2.22    ( ! [X4,X5] : (k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))),X4))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f1034,f32])).
% 14.61/2.22  fof(f1034,plain,(
% 14.61/2.22    ( ! [X4,X5] : (k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)))) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))))),X4))) )),
% 14.61/2.22    inference(superposition,[],[f640,f171])).
% 14.61/2.22  fof(f640,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f639,f32])).
% 14.61/2.22  fof(f639,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f628,f32])).
% 14.61/2.22  fof(f628,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)) = k1_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))))))) )),
% 14.61/2.22    inference(superposition,[],[f625,f164])).
% 14.61/2.22  fof(f164,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 14.61/2.22    inference(backward_demodulation,[],[f80,f158])).
% 14.61/2.22  fof(f80,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 14.61/2.22    inference(resolution,[],[f79,f57])).
% 14.61/2.22  fof(f625,plain,(
% 14.61/2.22    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X3))))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f624,f171])).
% 14.61/2.22  fof(f624,plain,(
% 14.61/2.22    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X4),X3))))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f614,f546])).
% 14.61/2.22  fof(f546,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1))))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f545,f32])).
% 14.61/2.22  fof(f545,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)))) = k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f544,f164])).
% 14.61/2.22  fof(f544,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f531,f225])).
% 14.61/2.22  fof(f531,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0)) = k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1))))) )),
% 14.61/2.22    inference(superposition,[],[f166,f222])).
% 14.61/2.22  fof(f222,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 14.61/2.22    inference(superposition,[],[f158,f158])).
% 14.61/2.22  fof(f614,plain,(
% 14.61/2.22    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X4),X3)))) = k4_xboole_0(X3,k1_relat_1(k7_relat_1(k6_relat_1(X3),k4_xboole_0(X3,X4))))) )),
% 14.61/2.22    inference(superposition,[],[f158,f242])).
% 14.61/2.22  fof(f242,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)))) )),
% 14.61/2.22    inference(backward_demodulation,[],[f223,f241])).
% 14.61/2.22  fof(f241,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(k4_xboole_0(X2,X3)),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),k4_xboole_0(X2,X3)))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f224,f222])).
% 14.61/2.22  fof(f224,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(k4_xboole_0(X2,X3)),X2)) = k4_xboole_0(X2,k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) )),
% 14.61/2.22    inference(superposition,[],[f166,f158])).
% 14.61/2.22  fof(f223,plain,(
% 14.61/2.22    ( ! [X0,X1] : (k4_xboole_0(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k1_relat_1(k7_relat_1(k6_relat_1(k4_xboole_0(X0,X1)),X0))) )),
% 14.61/2.22    inference(superposition,[],[f166,f166])).
% 14.61/2.22  fof(f2541,plain,(
% 14.61/2.22    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))),X2),k7_relat_1(k6_relat_1(X1),X2))) )),
% 14.61/2.22    inference(superposition,[],[f2445,f225])).
% 14.61/2.22  fof(f2445,plain,(
% 14.61/2.22    ( ! [X101,X102,X100] : (r1_tarski(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X100),X101))),X102),k7_relat_1(k6_relat_1(X101),X102))) )),
% 14.61/2.22    inference(superposition,[],[f1325,f1623])).
% 14.61/2.22  fof(f31087,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X2))),X2),X3)) )),
% 14.61/2.22    inference(backward_demodulation,[],[f1409,f30609])).
% 14.61/2.22  fof(f30609,plain,(
% 14.61/2.22    ( ! [X4,X5] : (k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) = k2_relat_1(k7_relat_1(k6_relat_1(X5),X4))) )),
% 14.61/2.22    inference(superposition,[],[f33,f27965])).
% 14.61/2.22  fof(f27965,plain,(
% 14.61/2.22    ( ! [X4,X5] : (k7_relat_1(k6_relat_1(X4),X5) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f27399,f1593])).
% 14.61/2.22  fof(f27399,plain,(
% 14.61/2.22    ( ! [X4,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X5),k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)))) )),
% 14.61/2.22    inference(backward_demodulation,[],[f836,f27386])).
% 14.61/2.22  fof(f836,plain,(
% 14.61/2.22    ( ! [X4,X5] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))),k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)))) )),
% 14.61/2.22    inference(superposition,[],[f164,f623])).
% 14.61/2.22  fof(f623,plain,(
% 14.61/2.22    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),X1))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f613,f546])).
% 14.61/2.22  fof(f613,plain,(
% 14.61/2.22    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),X1)) = k4_xboole_0(X1,k1_relat_1(k7_relat_1(k6_relat_1(X1),k4_xboole_0(X1,X2))))) )),
% 14.61/2.22    inference(superposition,[],[f166,f242])).
% 14.61/2.22  fof(f27406,plain,(
% 14.61/2.22    ( ! [X10,X11] : (k7_relat_1(k6_relat_1(X10),X11) = k7_relat_1(k7_relat_1(k6_relat_1(X10),X11),X10)) )),
% 14.61/2.22    inference(backward_demodulation,[],[f1632,f27386])).
% 14.61/2.22  fof(f1632,plain,(
% 14.61/2.22    ( ! [X10,X11] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X10),X11))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X10),X11))),X10)) )),
% 14.61/2.22    inference(forward_demodulation,[],[f1599,f1435])).
% 14.61/2.22  fof(f1435,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) )),
% 14.61/2.22    inference(forward_demodulation,[],[f1421,f33])).
% 14.61/2.22  fof(f1421,plain,(
% 14.61/2.22    ( ! [X2,X3] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))))),X2),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) )),
% 14.61/2.22    inference(superposition,[],[f1409,f164])).
% 14.61/2.22  fof(f1599,plain,(
% 14.61/2.22    ( ! [X10,X11] : (k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X10),X11))),X10) = k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X10),X11))),X10),k1_relat_1(k7_relat_1(k6_relat_1(X10),X11)))) )),
% 14.61/2.22    inference(superposition,[],[f1576,f640])).
% 14.61/2.22  fof(f30606,plain,(
% 14.61/2.22    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK1),sK0)),
% 14.61/2.22    inference(superposition,[],[f182,f27965])).
% 14.61/2.22  fof(f182,plain,(
% 14.61/2.22    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 14.61/2.22    inference(backward_demodulation,[],[f68,f158])).
% 14.61/2.22  fof(f68,plain,(
% 14.61/2.22    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 14.61/2.22    inference(backward_demodulation,[],[f56,f66])).
% 14.61/2.22  fof(f56,plain,(
% 14.61/2.22    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 14.61/2.22    inference(backward_demodulation,[],[f50,f53])).
% 14.61/2.22  fof(f50,plain,(
% 14.61/2.22    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 14.61/2.22    inference(definition_unfolding,[],[f30,f49])).
% 14.61/2.22  fof(f30,plain,(
% 14.61/2.22    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 14.61/2.22    inference(cnf_transformation,[],[f29])).
% 14.61/2.22  fof(f29,plain,(
% 14.61/2.22    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 14.61/2.22    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f28])).
% 14.61/2.22  fof(f28,plain,(
% 14.61/2.22    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 14.61/2.22    introduced(choice_axiom,[])).
% 14.61/2.22  fof(f19,plain,(
% 14.61/2.22    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 14.61/2.22    inference(ennf_transformation,[],[f17])).
% 14.61/2.22  fof(f17,negated_conjecture,(
% 14.61/2.22    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 14.61/2.22    inference(negated_conjecture,[],[f16])).
% 14.61/2.22  fof(f16,conjecture,(
% 14.61/2.22    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 14.61/2.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 14.61/2.22  % SZS output end Proof for theBenchmark
% 14.61/2.22  % (8286)------------------------------
% 14.61/2.22  % (8286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.61/2.22  % (8286)Termination reason: Refutation
% 14.61/2.22  
% 14.61/2.22  % (8286)Memory used [KB]: 34796
% 14.61/2.22  % (8286)Time elapsed: 1.806 s
% 14.61/2.22  % (8286)------------------------------
% 14.61/2.22  % (8286)------------------------------
% 14.61/2.23  % (8275)Success in time 1.872 s
%------------------------------------------------------------------------------
