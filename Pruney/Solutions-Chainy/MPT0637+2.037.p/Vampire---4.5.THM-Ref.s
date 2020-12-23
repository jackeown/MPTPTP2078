%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:27 EST 2020

% Result     : Theorem 3.20s
% Output     : Refutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 163 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  137 ( 269 expanded)
%              Number of equality atoms :   68 ( 117 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3840,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3838])).

fof(f3838,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f31,f3010])).

fof(f3010,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f59,f3008])).

fof(f3008,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f2981,f95])).

fof(f95,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2)) ),
    inference(resolution,[],[f70,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f69,f59])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f67,f34])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f2981,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f718,f801])).

fof(f801,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f790,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f61,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f790,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[],[f216,f66])).

fof(f66,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k6_relat_1(X0),k2_zfmisc_1(X1,X0)) ),
    inference(forward_demodulation,[],[f64,f34])).

fof(f64,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k6_relat_1(X0),k2_zfmisc_1(X1,k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f43,f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f216,plain,(
    ! [X0,X1] : k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4)
      | k3_xboole_0(k6_relat_1(X2),X3) = k7_relat_1(k3_xboole_0(k6_relat_1(X2),X3),X4) ) ),
    inference(forward_demodulation,[],[f72,f60])).

fof(f60,plain,(
    ! [X4,X2,X3] : k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X3),X4)) = k7_relat_1(k3_xboole_0(k6_relat_1(X3),X4),X2) ),
    inference(resolution,[],[f41,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f40,f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f72,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4)
      | k3_xboole_0(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X4),k3_xboole_0(k6_relat_1(X2),X3)) ) ),
    inference(resolution,[],[f45,f51])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f718,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),k3_xboole_0(X6,X5)) = k7_relat_1(k6_relat_1(X7),k3_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f711,f59])).

fof(f711,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),k3_xboole_0(X6,X5)) = k5_relat_1(k6_relat_1(k3_xboole_0(X6,X5)),k6_relat_1(X7)) ),
    inference(superposition,[],[f212,f96])).

fof(f96,plain,(
    ! [X4,X3] : k6_relat_1(k3_xboole_0(X3,X4)) = k7_relat_1(k6_relat_1(X4),k3_xboole_0(X3,X4)) ),
    inference(resolution,[],[f70,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f212,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f211,f59])).

fof(f211,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(forward_demodulation,[],[f206,f110])).

fof(f110,plain,(
    ! [X8,X7,X9] : k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X8),X9)) = k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7) ),
    inference(resolution,[],[f100,f41])).

fof(f100,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f51,f66])).

fof(f206,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(resolution,[],[f107,f32])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f104,f59])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f76,f32])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f59,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f41,f32])).

fof(f31,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27])).

fof(f27,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (10562)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.51  % (10578)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.51  % (10576)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (10553)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (10555)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (10577)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.51  % (10570)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.51  % (10564)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (10572)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (10562)Refutation not found, incomplete strategy% (10562)------------------------------
% 0.22/0.52  % (10562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10562)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10562)Memory used [KB]: 10618
% 0.22/0.52  % (10562)Time elapsed: 0.102 s
% 0.22/0.52  % (10562)------------------------------
% 0.22/0.52  % (10562)------------------------------
% 0.22/0.52  % (10560)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (10556)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (10560)Refutation not found, incomplete strategy% (10560)------------------------------
% 0.22/0.52  % (10560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10578)Refutation not found, incomplete strategy% (10578)------------------------------
% 0.22/0.52  % (10578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10576)Refutation not found, incomplete strategy% (10576)------------------------------
% 0.22/0.52  % (10576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10576)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10576)Memory used [KB]: 6140
% 0.22/0.52  % (10576)Time elapsed: 0.106 s
% 0.22/0.52  % (10576)------------------------------
% 0.22/0.52  % (10576)------------------------------
% 0.22/0.52  % (10578)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10578)Memory used [KB]: 10618
% 0.22/0.52  % (10578)Time elapsed: 0.105 s
% 0.22/0.52  % (10578)------------------------------
% 0.22/0.52  % (10578)------------------------------
% 0.22/0.52  % (10551)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (10551)Refutation not found, incomplete strategy% (10551)------------------------------
% 0.22/0.52  % (10551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10551)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10551)Memory used [KB]: 1663
% 0.22/0.52  % (10551)Time elapsed: 0.106 s
% 0.22/0.52  % (10551)------------------------------
% 0.22/0.52  % (10551)------------------------------
% 0.22/0.52  % (10550)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (10554)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (10568)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (10568)Refutation not found, incomplete strategy% (10568)------------------------------
% 0.22/0.53  % (10568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10568)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10568)Memory used [KB]: 1663
% 0.22/0.53  % (10568)Time elapsed: 0.104 s
% 0.22/0.53  % (10568)------------------------------
% 0.22/0.53  % (10568)------------------------------
% 0.22/0.53  % (10564)Refutation not found, incomplete strategy% (10564)------------------------------
% 0.22/0.53  % (10564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10564)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10564)Memory used [KB]: 1663
% 0.22/0.53  % (10564)Time elapsed: 0.081 s
% 0.22/0.53  % (10564)------------------------------
% 0.22/0.53  % (10564)------------------------------
% 0.22/0.53  % (10560)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10560)Memory used [KB]: 10618
% 0.22/0.53  % (10560)Time elapsed: 0.111 s
% 0.22/0.53  % (10560)------------------------------
% 0.22/0.53  % (10560)------------------------------
% 0.22/0.53  % (10575)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (10575)Refutation not found, incomplete strategy% (10575)------------------------------
% 0.22/0.53  % (10575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10575)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10575)Memory used [KB]: 6140
% 0.22/0.53  % (10575)Time elapsed: 0.119 s
% 0.22/0.53  % (10575)------------------------------
% 0.22/0.53  % (10575)------------------------------
% 0.22/0.53  % (10574)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (10561)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (10552)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (10561)Refutation not found, incomplete strategy% (10561)------------------------------
% 0.22/0.53  % (10561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10561)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10561)Memory used [KB]: 6140
% 0.22/0.53  % (10561)Time elapsed: 0.135 s
% 0.22/0.53  % (10561)------------------------------
% 0.22/0.53  % (10561)------------------------------
% 0.22/0.53  % (10574)Refutation not found, incomplete strategy% (10574)------------------------------
% 0.22/0.53  % (10574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10574)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10574)Memory used [KB]: 10618
% 0.22/0.53  % (10574)Time elapsed: 0.127 s
% 0.22/0.53  % (10574)------------------------------
% 0.22/0.53  % (10574)------------------------------
% 0.22/0.53  % (10569)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (10566)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (10563)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (10565)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (10566)Refutation not found, incomplete strategy% (10566)------------------------------
% 0.22/0.54  % (10566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10566)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10566)Memory used [KB]: 10618
% 0.22/0.54  % (10566)Time elapsed: 0.130 s
% 0.22/0.54  % (10566)------------------------------
% 0.22/0.54  % (10566)------------------------------
% 0.22/0.54  % (10571)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (10567)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (10567)Refutation not found, incomplete strategy% (10567)------------------------------
% 0.22/0.54  % (10567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10567)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10567)Memory used [KB]: 1663
% 0.22/0.54  % (10567)Time elapsed: 0.129 s
% 0.22/0.54  % (10567)------------------------------
% 0.22/0.54  % (10567)------------------------------
% 0.22/0.54  % (10559)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (10558)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (10577)Refutation not found, incomplete strategy% (10577)------------------------------
% 0.22/0.55  % (10577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10577)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10577)Memory used [KB]: 6140
% 0.22/0.55  % (10577)Time elapsed: 0.114 s
% 0.22/0.55  % (10577)------------------------------
% 0.22/0.55  % (10577)------------------------------
% 0.22/0.55  % (10557)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (10579)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (10579)Refutation not found, incomplete strategy% (10579)------------------------------
% 0.22/0.55  % (10579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10579)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10579)Memory used [KB]: 1663
% 0.22/0.55  % (10579)Time elapsed: 0.001 s
% 0.22/0.55  % (10579)------------------------------
% 0.22/0.55  % (10579)------------------------------
% 0.22/0.55  % (10573)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.93/0.60  % (10553)Refutation not found, incomplete strategy% (10553)------------------------------
% 1.93/0.60  % (10553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.61  % (10581)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.93/0.61  % (10553)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.61  
% 1.93/0.61  % (10553)Memory used [KB]: 6140
% 1.93/0.61  % (10553)Time elapsed: 0.196 s
% 1.93/0.61  % (10553)------------------------------
% 1.93/0.61  % (10553)------------------------------
% 1.93/0.62  % (10583)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.93/0.62  % (10587)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.93/0.62  % (10583)Refutation not found, incomplete strategy% (10583)------------------------------
% 1.93/0.62  % (10583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.62  % (10583)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.62  
% 1.93/0.62  % (10583)Memory used [KB]: 10618
% 1.93/0.62  % (10583)Time elapsed: 0.039 s
% 1.93/0.62  % (10583)------------------------------
% 1.93/0.62  % (10583)------------------------------
% 1.93/0.62  % (10587)Refutation not found, incomplete strategy% (10587)------------------------------
% 1.93/0.62  % (10587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.62  % (10587)Termination reason: Refutation not found, incomplete strategy
% 1.93/0.62  
% 1.93/0.62  % (10587)Memory used [KB]: 10618
% 1.93/0.62  % (10587)Time elapsed: 0.068 s
% 1.93/0.62  % (10587)------------------------------
% 1.93/0.62  % (10587)------------------------------
% 2.17/0.65  % (10580)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.17/0.65  % (10582)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.17/0.66  % (10552)Refutation not found, incomplete strategy% (10552)------------------------------
% 2.17/0.66  % (10552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.66  % (10552)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.66  
% 2.17/0.66  % (10552)Memory used [KB]: 6140
% 2.17/0.66  % (10552)Time elapsed: 0.248 s
% 2.17/0.66  % (10552)------------------------------
% 2.17/0.66  % (10552)------------------------------
% 2.17/0.66  % (10589)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.17/0.66  % (10565)Refutation not found, incomplete strategy% (10565)------------------------------
% 2.17/0.66  % (10565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.66  % (10565)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.66  
% 2.17/0.66  % (10565)Memory used [KB]: 6140
% 2.17/0.66  % (10565)Time elapsed: 0.241 s
% 2.17/0.66  % (10565)------------------------------
% 2.17/0.66  % (10565)------------------------------
% 2.17/0.66  % (10588)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.17/0.67  % (10586)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.17/0.67  % (10590)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.17/0.67  % (10586)Refutation not found, incomplete strategy% (10586)------------------------------
% 2.17/0.67  % (10586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.67  % (10586)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.67  
% 2.17/0.67  % (10586)Memory used [KB]: 1663
% 2.17/0.67  % (10586)Time elapsed: 0.107 s
% 2.17/0.67  % (10586)------------------------------
% 2.17/0.67  % (10586)------------------------------
% 2.17/0.67  % (10590)Refutation not found, incomplete strategy% (10590)------------------------------
% 2.17/0.67  % (10590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.67  % (10590)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.67  
% 2.17/0.67  % (10590)Memory used [KB]: 10618
% 2.17/0.67  % (10590)Time elapsed: 0.106 s
% 2.17/0.67  % (10590)------------------------------
% 2.17/0.67  % (10590)------------------------------
% 2.17/0.67  % (10585)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.17/0.67  % (10585)Refutation not found, incomplete strategy% (10585)------------------------------
% 2.17/0.67  % (10585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.67  % (10585)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.67  
% 2.17/0.67  % (10585)Memory used [KB]: 10618
% 2.17/0.67  % (10585)Time elapsed: 0.107 s
% 2.17/0.67  % (10585)------------------------------
% 2.17/0.67  % (10585)------------------------------
% 2.17/0.67  % (10591)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.17/0.67  % (10593)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.17/0.68  % (10592)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.17/0.68  % (10558)Refutation not found, incomplete strategy% (10558)------------------------------
% 2.17/0.68  % (10558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (10558)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (10558)Memory used [KB]: 6268
% 2.17/0.68  % (10558)Time elapsed: 0.280 s
% 2.17/0.68  % (10558)------------------------------
% 2.17/0.68  % (10558)------------------------------
% 2.17/0.69  % (10594)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.17/0.69  % (10594)Refutation not found, incomplete strategy% (10594)------------------------------
% 2.17/0.69  % (10594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (10594)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (10594)Memory used [KB]: 10618
% 2.17/0.69  % (10594)Time elapsed: 0.106 s
% 2.17/0.69  % (10594)------------------------------
% 2.17/0.69  % (10594)------------------------------
% 2.17/0.69  % (10592)Refutation not found, incomplete strategy% (10592)------------------------------
% 2.17/0.69  % (10592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (10592)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (10592)Memory used [KB]: 10618
% 2.17/0.69  % (10592)Time elapsed: 0.117 s
% 2.17/0.69  % (10592)------------------------------
% 2.17/0.69  % (10592)------------------------------
% 2.17/0.72  % (10595)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.78/0.72  % (10596)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.78/0.76  % (10598)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.78/0.77  % (10601)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.78/0.77  % (10597)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.78/0.79  % (10589)Refutation not found, incomplete strategy% (10589)------------------------------
% 2.78/0.79  % (10589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.79  % (10589)Termination reason: Refutation not found, incomplete strategy
% 2.78/0.79  
% 2.78/0.79  % (10589)Memory used [KB]: 6268
% 2.78/0.79  % (10589)Time elapsed: 0.204 s
% 2.78/0.79  % (10589)------------------------------
% 2.78/0.79  % (10589)------------------------------
% 3.20/0.80  % (10600)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.20/0.80  % (10600)Refutation not found, incomplete strategy% (10600)------------------------------
% 3.20/0.80  % (10600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.80  % (10600)Termination reason: Refutation not found, incomplete strategy
% 3.20/0.80  
% 3.20/0.80  % (10600)Memory used [KB]: 1663
% 3.20/0.80  % (10600)Time elapsed: 0.105 s
% 3.20/0.80  % (10600)------------------------------
% 3.20/0.80  % (10600)------------------------------
% 3.20/0.81  % (10599)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 3.20/0.82  % (10595)Refutation not found, incomplete strategy% (10595)------------------------------
% 3.20/0.82  % (10595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.82  % (10595)Termination reason: Refutation not found, incomplete strategy
% 3.20/0.82  
% 3.20/0.82  % (10595)Memory used [KB]: 6140
% 3.20/0.82  % (10595)Time elapsed: 0.143 s
% 3.20/0.82  % (10595)------------------------------
% 3.20/0.82  % (10595)------------------------------
% 3.20/0.83  % (10596)Refutation not found, incomplete strategy% (10596)------------------------------
% 3.20/0.83  % (10596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.84  % (10596)Termination reason: Refutation not found, incomplete strategy
% 3.20/0.84  
% 3.20/0.84  % (10596)Memory used [KB]: 6140
% 3.20/0.84  % (10596)Time elapsed: 0.148 s
% 3.20/0.84  % (10596)------------------------------
% 3.20/0.84  % (10596)------------------------------
% 3.20/0.86  % (10557)Refutation found. Thanks to Tanya!
% 3.20/0.86  % SZS status Theorem for theBenchmark
% 3.20/0.86  % SZS output start Proof for theBenchmark
% 3.20/0.86  fof(f3840,plain,(
% 3.20/0.86    $false),
% 3.20/0.86    inference(trivial_inequality_removal,[],[f3838])).
% 3.20/0.86  fof(f3838,plain,(
% 3.20/0.86    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.20/0.86    inference(superposition,[],[f31,f3010])).
% 3.20/0.86  fof(f3010,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(k3_xboole_0(X1,X0))) )),
% 3.20/0.86    inference(backward_demodulation,[],[f59,f3008])).
% 3.20/0.86  fof(f3008,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 3.20/0.86    inference(forward_demodulation,[],[f2981,f95])).
% 3.20/0.86  fof(f95,plain,(
% 3.20/0.86    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2))) )),
% 3.20/0.86    inference(resolution,[],[f70,f36])).
% 3.20/0.86  fof(f36,plain,(
% 3.20/0.86    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.20/0.86    inference(cnf_transformation,[],[f3])).
% 3.20/0.86  fof(f3,axiom,(
% 3.20/0.86    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.20/0.86  fof(f70,plain,(
% 3.20/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.20/0.86    inference(forward_demodulation,[],[f69,f59])).
% 3.20/0.86  fof(f69,plain,(
% 3.20/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 3.20/0.86    inference(forward_demodulation,[],[f67,f34])).
% 3.20/0.86  fof(f34,plain,(
% 3.20/0.86    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.20/0.86    inference(cnf_transformation,[],[f9])).
% 3.20/0.86  fof(f9,axiom,(
% 3.20/0.86    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.20/0.86  fof(f67,plain,(
% 3.20/0.86    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 3.20/0.86    inference(resolution,[],[f44,f32])).
% 3.20/0.86  fof(f32,plain,(
% 3.20/0.86    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.20/0.86    inference(cnf_transformation,[],[f6])).
% 3.20/0.86  fof(f6,axiom,(
% 3.20/0.86    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 3.20/0.86  fof(f44,plain,(
% 3.20/0.86    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 3.20/0.86    inference(cnf_transformation,[],[f24])).
% 3.20/0.86  fof(f24,plain,(
% 3.20/0.86    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.20/0.86    inference(flattening,[],[f23])).
% 3.20/0.86  fof(f23,plain,(
% 3.20/0.86    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.20/0.86    inference(ennf_transformation,[],[f11])).
% 3.20/0.86  fof(f11,axiom,(
% 3.20/0.86    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 3.20/0.86  fof(f2981,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 3.20/0.86    inference(superposition,[],[f718,f801])).
% 3.20/0.86  fof(f801,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k3_xboole_0(X0,X1))) )),
% 3.20/0.86    inference(forward_demodulation,[],[f790,f63])).
% 3.20/0.86  fof(f63,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 3.20/0.86    inference(forward_demodulation,[],[f61,f33])).
% 3.20/0.86  fof(f33,plain,(
% 3.20/0.86    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.20/0.86    inference(cnf_transformation,[],[f9])).
% 3.20/0.86  fof(f61,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 3.20/0.86    inference(resolution,[],[f42,f32])).
% 3.20/0.86  fof(f42,plain,(
% 3.20/0.86    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 3.20/0.86    inference(cnf_transformation,[],[f21])).
% 3.20/0.86  fof(f21,plain,(
% 3.20/0.86    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.20/0.86    inference(ennf_transformation,[],[f12])).
% 3.20/0.86  fof(f12,axiom,(
% 3.20/0.86    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 3.20/0.86  fof(f790,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 3.20/0.86    inference(superposition,[],[f216,f66])).
% 3.20/0.86  fof(f66,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k6_relat_1(X0),k2_zfmisc_1(X1,X0))) )),
% 3.20/0.86    inference(forward_demodulation,[],[f64,f34])).
% 3.20/0.86  fof(f64,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(k6_relat_1(X0),k2_zfmisc_1(X1,k2_relat_1(k6_relat_1(X0))))) )),
% 3.20/0.86    inference(resolution,[],[f43,f32])).
% 3.20/0.86  fof(f43,plain,(
% 3.20/0.86    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) )),
% 3.20/0.86    inference(cnf_transformation,[],[f22])).
% 3.20/0.86  fof(f22,plain,(
% 3.20/0.86    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.20/0.86    inference(ennf_transformation,[],[f14])).
% 3.20/0.86  fof(f14,axiom,(
% 3.20/0.86    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).
% 3.20/0.86  fof(f216,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)))) )),
% 3.20/0.86    inference(resolution,[],[f75,f49])).
% 3.20/0.86  fof(f49,plain,(
% 3.20/0.86    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.20/0.86    inference(equality_resolution,[],[f47])).
% 3.20/0.86  fof(f47,plain,(
% 3.20/0.86    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.20/0.86    inference(cnf_transformation,[],[f30])).
% 3.20/0.86  fof(f30,plain,(
% 3.20/0.86    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/0.86    inference(flattening,[],[f29])).
% 3.20/0.86  fof(f29,plain,(
% 3.20/0.86    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/0.86    inference(nnf_transformation,[],[f2])).
% 3.20/0.86  fof(f2,axiom,(
% 3.20/0.86    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.20/0.86  fof(f75,plain,(
% 3.20/0.86    ( ! [X4,X2,X3] : (~r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4) | k3_xboole_0(k6_relat_1(X2),X3) = k7_relat_1(k3_xboole_0(k6_relat_1(X2),X3),X4)) )),
% 3.20/0.86    inference(forward_demodulation,[],[f72,f60])).
% 3.20/0.86  fof(f60,plain,(
% 3.20/0.86    ( ! [X4,X2,X3] : (k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X3),X4)) = k7_relat_1(k3_xboole_0(k6_relat_1(X3),X4),X2)) )),
% 3.20/0.86    inference(resolution,[],[f41,f51])).
% 3.20/0.86  fof(f51,plain,(
% 3.20/0.86    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) )),
% 3.20/0.86    inference(resolution,[],[f40,f32])).
% 3.20/0.86  fof(f40,plain,(
% 3.20/0.86    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 3.20/0.86    inference(cnf_transformation,[],[f19])).
% 3.20/0.86  fof(f19,plain,(
% 3.20/0.86    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 3.20/0.86    inference(ennf_transformation,[],[f7])).
% 3.20/0.86  fof(f7,axiom,(
% 3.20/0.86    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 3.20/0.86  fof(f41,plain,(
% 3.20/0.86    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 3.20/0.86    inference(cnf_transformation,[],[f20])).
% 3.20/0.86  fof(f20,plain,(
% 3.20/0.86    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.20/0.86    inference(ennf_transformation,[],[f13])).
% 3.20/0.86  fof(f13,axiom,(
% 3.20/0.86    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 3.20/0.86  fof(f72,plain,(
% 3.20/0.86    ( ! [X4,X2,X3] : (~r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4) | k3_xboole_0(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X4),k3_xboole_0(k6_relat_1(X2),X3))) )),
% 3.20/0.86    inference(resolution,[],[f45,f51])).
% 3.20/0.86  fof(f45,plain,(
% 3.20/0.86    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 3.20/0.86    inference(cnf_transformation,[],[f26])).
% 3.20/0.86  fof(f26,plain,(
% 3.20/0.86    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.20/0.86    inference(flattening,[],[f25])).
% 3.20/0.86  fof(f25,plain,(
% 3.20/0.86    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.20/0.86    inference(ennf_transformation,[],[f10])).
% 3.20/0.86  fof(f10,axiom,(
% 3.20/0.86    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 3.20/0.86  fof(f718,plain,(
% 3.20/0.86    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),k3_xboole_0(X6,X5)) = k7_relat_1(k6_relat_1(X7),k3_xboole_0(X6,X5))) )),
% 3.20/0.86    inference(forward_demodulation,[],[f711,f59])).
% 3.20/0.86  fof(f711,plain,(
% 3.20/0.86    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),k3_xboole_0(X6,X5)) = k5_relat_1(k6_relat_1(k3_xboole_0(X6,X5)),k6_relat_1(X7))) )),
% 3.20/0.86    inference(superposition,[],[f212,f96])).
% 3.20/0.86  fof(f96,plain,(
% 3.20/0.86    ( ! [X4,X3] : (k6_relat_1(k3_xboole_0(X3,X4)) = k7_relat_1(k6_relat_1(X4),k3_xboole_0(X3,X4))) )),
% 3.20/0.86    inference(resolution,[],[f70,f52])).
% 3.20/0.86  fof(f52,plain,(
% 3.20/0.86    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 3.20/0.86    inference(superposition,[],[f36,f37])).
% 3.20/0.86  fof(f37,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.20/0.86    inference(cnf_transformation,[],[f1])).
% 3.20/0.86  fof(f1,axiom,(
% 3.20/0.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.20/0.86  fof(f212,plain,(
% 3.20/0.86    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 3.20/0.86    inference(forward_demodulation,[],[f211,f59])).
% 3.20/0.86  fof(f211,plain,(
% 3.20/0.86    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) )),
% 3.20/0.86    inference(forward_demodulation,[],[f206,f110])).
% 3.20/0.86  fof(f110,plain,(
% 3.20/0.86    ( ! [X8,X7,X9] : (k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X8),X9)) = k7_relat_1(k7_relat_1(k6_relat_1(X8),X9),X7)) )),
% 3.20/0.86    inference(resolution,[],[f100,f41])).
% 3.20/0.86  fof(f100,plain,(
% 3.20/0.86    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 3.20/0.86    inference(superposition,[],[f51,f66])).
% 3.20/0.86  fof(f206,plain,(
% 3.20/0.86    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 3.20/0.86    inference(resolution,[],[f107,f32])).
% 3.20/0.86  fof(f107,plain,(
% 3.20/0.86    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 3.20/0.86    inference(forward_demodulation,[],[f104,f59])).
% 3.20/0.86  fof(f104,plain,(
% 3.20/0.86    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 3.20/0.86    inference(resolution,[],[f76,f32])).
% 3.20/0.86  fof(f76,plain,(
% 3.20/0.86    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 3.20/0.86    inference(resolution,[],[f35,f32])).
% 3.20/0.86  fof(f35,plain,(
% 3.20/0.86    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.20/0.86    inference(cnf_transformation,[],[f18])).
% 3.20/0.86  fof(f18,plain,(
% 3.20/0.86    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.20/0.86    inference(ennf_transformation,[],[f8])).
% 3.20/0.86  fof(f8,axiom,(
% 3.20/0.86    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 3.20/0.86  fof(f59,plain,(
% 3.20/0.86    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.20/0.86    inference(resolution,[],[f41,f32])).
% 3.20/0.86  fof(f31,plain,(
% 3.20/0.86    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.20/0.86    inference(cnf_transformation,[],[f28])).
% 3.20/0.86  fof(f28,plain,(
% 3.20/0.86    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.20/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27])).
% 3.20/0.86  fof(f27,plain,(
% 3.20/0.86    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.20/0.86    introduced(choice_axiom,[])).
% 3.20/0.86  fof(f17,plain,(
% 3.20/0.86    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.20/0.86    inference(ennf_transformation,[],[f16])).
% 3.20/0.86  fof(f16,negated_conjecture,(
% 3.20/0.86    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.20/0.86    inference(negated_conjecture,[],[f15])).
% 3.20/0.86  fof(f15,conjecture,(
% 3.20/0.86    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.20/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 3.20/0.86  % SZS output end Proof for theBenchmark
% 3.20/0.86  % (10557)------------------------------
% 3.20/0.86  % (10557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.86  % (10557)Termination reason: Refutation
% 3.20/0.86  
% 3.20/0.86  % (10557)Memory used [KB]: 5628
% 3.20/0.86  % (10557)Time elapsed: 0.426 s
% 3.20/0.86  % (10557)------------------------------
% 3.20/0.86  % (10557)------------------------------
% 3.20/0.86  % (10549)Success in time 0.489 s
%------------------------------------------------------------------------------
