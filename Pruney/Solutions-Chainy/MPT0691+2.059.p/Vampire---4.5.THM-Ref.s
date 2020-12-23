%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 530 expanded)
%              Number of leaves         :   18 ( 140 expanded)
%              Depth                    :   27
%              Number of atoms          :  218 (1253 expanded)
%              Number of equality atoms :   87 ( 283 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f558,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f557])).

fof(f557,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f552,f257])).

fof(f257,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f137,f131])).

fof(f131,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(resolution,[],[f76,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f68,f67])).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f137,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X0))) ),
    inference(resolution,[],[f79,f81])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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

fof(f552,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f172,f551])).

fof(f551,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f550,f463])).

fof(f463,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f459,f44])).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f459,plain,
    ( ~ v1_relat_1(sK1)
    | sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f435,f65])).

fof(f65,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f435,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | sK0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f425,f108])).

fof(f108,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X7,k1_relat_1(k7_relat_1(X6,X7)))
      | k1_relat_1(k7_relat_1(X6,X7)) = X7
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f54,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f425,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f188,f417])).

fof(f417,plain,(
    sK0 = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(resolution,[],[f416,f44])).

fof(f416,plain,
    ( ~ v1_relat_1(sK1)
    | sK0 = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(resolution,[],[f405,f65])).

fof(f405,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | sK0 = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f404,f130])).

fof(f130,plain,(
    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f76,f45])).

fof(f45,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f404,plain,
    ( k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f403,f173])).

fof(f173,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f169,f87])).

fof(f87,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f48,f44])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f169,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f75,f44])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f403,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(sK1)) = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f402,f194])).

fof(f194,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f191,f61])).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f191,plain,(
    ! [X0] : k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) ),
    inference(resolution,[],[f177,f65])).

fof(f177,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(sK1,k1_relat_1(X0)) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK1)))) ) ),
    inference(resolution,[],[f58,f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f402,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))) = k10_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)))),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f398,f173])).

fof(f398,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))) = k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0)) ),
    inference(resolution,[],[f361,f188])).

fof(f361,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X7,k1_relat_1(k7_relat_1(X6,sK0)))
      | k1_setfam_1(k1_enumset1(X7,X7,k1_relat_1(sK1))) = X7
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f354,f56])).

fof(f354,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,sK0)
      | ~ r1_tarski(X1,X2)
      | k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK1))) = X1 ) ),
    inference(resolution,[],[f335,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f335,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK1))) = X0 ) ),
    inference(resolution,[],[f133,f45])).

fof(f133,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X5,X4)
      | ~ r1_tarski(X3,X5)
      | k1_setfam_1(k1_enumset1(X3,X3,X4)) = X3 ) ),
    inference(resolution,[],[f76,f51])).

fof(f188,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f56,f187])).

fof(f187,plain,(
    ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f184,f61])).

fof(f184,plain,(
    ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))))) ),
    inference(resolution,[],[f174,f65])).

fof(f174,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(sK1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(X0)))) ) ),
    inference(resolution,[],[f58,f44])).

fof(f550,plain,(
    k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f456,f545])).

fof(f545,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f544,f267])).

fof(f267,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK1,X0),X0) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f158,f44])).

fof(f158,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(k7_relat_1(X2,X1),X1) = k9_relat_1(X2,X1) ) ),
    inference(resolution,[],[f49,f81])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f544,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0) ),
    inference(superposition,[],[f460,f463])).

fof(f460,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f96,f44])).

fof(f96,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f50,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f456,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f89,f44])).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f48,f60])).

fof(f172,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f149,f169])).

fof(f149,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))))) ),
    inference(resolution,[],[f80,f46])).

fof(f46,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:50:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (13239)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (13231)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (13223)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (13225)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (13217)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (13219)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (13218)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (13241)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (13220)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (13233)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (13221)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (13243)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (13222)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (13232)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (13242)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (13230)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (13235)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (13244)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (13240)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (13245)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (13226)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (13227)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (13236)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (13246)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (13237)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (13228)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (13234)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (13229)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (13238)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (13224)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.58  % (13222)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f558,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f557])).
% 0.21/0.58  fof(f557,plain,(
% 0.21/0.58    k1_xboole_0 != k1_xboole_0),
% 0.21/0.58    inference(superposition,[],[f552,f257])).
% 0.21/0.58  fof(f257,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.58    inference(forward_demodulation,[],[f137,f131])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.21/0.58    inference(resolution,[],[f76,f81])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.58    inference(equality_resolution,[],[f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f42])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.58    inference(flattening,[],[f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.58    inference(nnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.58  fof(f76,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f55,f72])).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f68,f67])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.58  fof(f137,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X0)))) )),
% 0.21/0.58    inference(resolution,[],[f79,f81])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f70,f73])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f71,f72])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.58    inference(nnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.58  fof(f552,plain,(
% 0.21/0.58    k1_xboole_0 != k5_xboole_0(sK0,sK0)),
% 0.21/0.58    inference(backward_demodulation,[],[f172,f551])).
% 0.21/0.58  fof(f551,plain,(
% 0.21/0.58    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 0.21/0.58    inference(forward_demodulation,[],[f550,f463])).
% 0.21/0.58  fof(f463,plain,(
% 0.21/0.58    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.58    inference(resolution,[],[f459,f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    v1_relat_1(sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f39])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.60    inference(flattening,[],[f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f25])).
% 0.21/0.60  fof(f25,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.60    inference(negated_conjecture,[],[f24])).
% 0.21/0.60  fof(f24,conjecture,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.60  fof(f459,plain,(
% 0.21/0.60    ~v1_relat_1(sK1) | sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.60    inference(resolution,[],[f435,f65])).
% 0.21/0.60  fof(f65,plain,(
% 0.21/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,axiom,(
% 0.21/0.60    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.60  fof(f435,plain,(
% 0.21/0.60    ~v1_relat_1(k6_relat_1(sK0)) | sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 0.21/0.60    inference(resolution,[],[f425,f108])).
% 0.21/0.60  fof(f108,plain,(
% 0.21/0.60    ( ! [X6,X7] : (~r1_tarski(X7,k1_relat_1(k7_relat_1(X6,X7))) | k1_relat_1(k7_relat_1(X6,X7)) = X7 | ~v1_relat_1(X6)) )),
% 0.21/0.60    inference(resolution,[],[f54,f56])).
% 0.21/0.60  fof(f56,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f35])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f20])).
% 0.21/0.60  fof(f20,axiom,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f42])).
% 0.21/0.60  fof(f425,plain,(
% 0.21/0.60    r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.21/0.60    inference(superposition,[],[f188,f417])).
% 0.21/0.60  fof(f417,plain,(
% 0.21/0.60    sK0 = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)))),
% 0.21/0.60    inference(resolution,[],[f416,f44])).
% 0.21/0.60  fof(f416,plain,(
% 0.21/0.60    ~v1_relat_1(sK1) | sK0 = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)))),
% 0.21/0.60    inference(resolution,[],[f405,f65])).
% 0.21/0.60  fof(f405,plain,(
% 0.21/0.60    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | sK0 = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)))),
% 0.21/0.60    inference(forward_demodulation,[],[f404,f130])).
% 0.21/0.60  fof(f130,plain,(
% 0.21/0.60    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))),
% 0.21/0.60    inference(resolution,[],[f76,f45])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.60    inference(cnf_transformation,[],[f40])).
% 0.21/0.60  fof(f404,plain,(
% 0.21/0.60    k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.21/0.60    inference(forward_demodulation,[],[f403,f173])).
% 0.21/0.60  fof(f173,plain,(
% 0.21/0.60    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK1)))) )),
% 0.21/0.60    inference(superposition,[],[f169,f87])).
% 0.21/0.60  fof(f87,plain,(
% 0.21/0.60    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.21/0.60    inference(resolution,[],[f48,f44])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f17])).
% 0.21/0.60  fof(f17,axiom,(
% 0.21/0.60    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.60  fof(f169,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK1,X1)))) )),
% 0.21/0.60    inference(resolution,[],[f75,f44])).
% 0.21/0.60  fof(f75,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f47,f72])).
% 0.21/0.60  fof(f47,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.60    inference(ennf_transformation,[],[f23])).
% 0.21/0.60  fof(f23,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 0.21/0.60  fof(f403,plain,(
% 0.21/0.60    k10_relat_1(k7_relat_1(sK1,sK0),k2_relat_1(sK1)) = k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.21/0.60    inference(forward_demodulation,[],[f402,f194])).
% 0.21/0.60  fof(f194,plain,(
% 0.21/0.60    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f191,f61])).
% 0.21/0.60  fof(f61,plain,(
% 0.21/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f19])).
% 0.21/0.60  fof(f19,axiom,(
% 0.21/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.60  fof(f191,plain,(
% 0.21/0.60    ( ! [X0] : (k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))))) )),
% 0.21/0.60    inference(resolution,[],[f177,f65])).
% 0.21/0.60  fof(f177,plain,(
% 0.21/0.60    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(sK1,k1_relat_1(X0)) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK1))))) )),
% 0.21/0.60    inference(resolution,[],[f58,f44])).
% 0.21/0.60  fof(f58,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f36])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f18])).
% 0.21/0.60  fof(f18,axiom,(
% 0.21/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 0.21/0.60  fof(f402,plain,(
% 0.21/0.60    k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))) = k10_relat_1(k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)))),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.21/0.60    inference(forward_demodulation,[],[f398,f173])).
% 0.21/0.60  fof(f398,plain,(
% 0.21/0.60    k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))) = k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),k1_relat_1(sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(sK0))),
% 0.21/0.60    inference(resolution,[],[f361,f188])).
% 0.21/0.60  fof(f361,plain,(
% 0.21/0.60    ( ! [X6,X7] : (~r1_tarski(X7,k1_relat_1(k7_relat_1(X6,sK0))) | k1_setfam_1(k1_enumset1(X7,X7,k1_relat_1(sK1))) = X7 | ~v1_relat_1(X6)) )),
% 0.21/0.60    inference(resolution,[],[f354,f56])).
% 0.21/0.60  fof(f354,plain,(
% 0.21/0.60    ( ! [X2,X1] : (~r1_tarski(X2,sK0) | ~r1_tarski(X1,X2) | k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(sK1))) = X1) )),
% 0.21/0.60    inference(resolution,[],[f335,f51])).
% 0.21/0.60  fof(f51,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.60    inference(flattening,[],[f32])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.60    inference(ennf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.60  fof(f335,plain,(
% 0.21/0.60    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK1))) = X0) )),
% 0.21/0.60    inference(resolution,[],[f133,f45])).
% 0.21/0.60  fof(f133,plain,(
% 0.21/0.60    ( ! [X4,X5,X3] : (~r1_tarski(X5,X4) | ~r1_tarski(X3,X5) | k1_setfam_1(k1_enumset1(X3,X3,X4)) = X3) )),
% 0.21/0.60    inference(resolution,[],[f76,f51])).
% 0.21/0.60  fof(f188,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.60    inference(superposition,[],[f56,f187])).
% 0.21/0.60  fof(f187,plain,(
% 0.21/0.60    ( ! [X0] : (k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f184,f61])).
% 0.21/0.60  fof(f184,plain,(
% 0.21/0.60    ( ! [X0] : (k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0)))))) )),
% 0.21/0.60    inference(resolution,[],[f174,f65])).
% 0.21/0.60  fof(f174,plain,(
% 0.21/0.60    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(sK1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(X0))))) )),
% 0.21/0.60    inference(resolution,[],[f58,f44])).
% 0.21/0.60  fof(f550,plain,(
% 0.21/0.60    k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.60    inference(superposition,[],[f456,f545])).
% 0.21/0.60  fof(f545,plain,(
% 0.21/0.60    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.60    inference(forward_demodulation,[],[f544,f267])).
% 0.21/0.60  fof(f267,plain,(
% 0.21/0.60    ( ! [X0] : (k9_relat_1(k7_relat_1(sK1,X0),X0) = k9_relat_1(sK1,X0)) )),
% 0.21/0.60    inference(resolution,[],[f158,f44])).
% 0.21/0.60  fof(f158,plain,(
% 0.21/0.60    ( ! [X2,X1] : (~v1_relat_1(X2) | k9_relat_1(k7_relat_1(X2,X1),X1) = k9_relat_1(X2,X1)) )),
% 0.21/0.60    inference(resolution,[],[f49,f81])).
% 0.21/0.60  fof(f49,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X0) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f30])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,axiom,(
% 0.21/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.21/0.60  fof(f544,plain,(
% 0.21/0.60    k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(k7_relat_1(sK1,sK0),sK0)),
% 0.21/0.60    inference(superposition,[],[f460,f463])).
% 0.21/0.60  fof(f460,plain,(
% 0.21/0.60    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.21/0.60    inference(resolution,[],[f96,f44])).
% 0.21/0.60  fof(f96,plain,(
% 0.21/0.60    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))) )),
% 0.21/0.60    inference(resolution,[],[f50,f60])).
% 0.21/0.60  fof(f60,plain,(
% 0.21/0.60    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f38])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f14])).
% 0.21/0.60  fof(f14,axiom,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.60  fof(f50,plain,(
% 0.21/0.60    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f31])).
% 0.21/0.60  fof(f31,plain,(
% 0.21/0.60    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f15])).
% 0.21/0.60  fof(f15,axiom,(
% 0.21/0.60    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.60  fof(f456,plain,(
% 0.21/0.60    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.21/0.60    inference(resolution,[],[f89,f44])).
% 0.21/0.60  fof(f89,plain,(
% 0.21/0.60    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))) )),
% 0.21/0.60    inference(resolution,[],[f48,f60])).
% 0.21/0.60  fof(f172,plain,(
% 0.21/0.60    k1_xboole_0 != k5_xboole_0(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)))),
% 0.21/0.60    inference(backward_demodulation,[],[f149,f169])).
% 0.21/0.60  fof(f149,plain,(
% 0.21/0.60    k1_xboole_0 != k5_xboole_0(sK0,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))))),
% 0.21/0.60    inference(resolution,[],[f80,f46])).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 0.21/0.60    inference(cnf_transformation,[],[f40])).
% 0.21/0.60  fof(f80,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f69,f73])).
% 0.21/0.60  fof(f69,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f43])).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (13222)------------------------------
% 0.21/0.60  % (13222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (13222)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (13222)Memory used [KB]: 2046
% 0.21/0.60  % (13222)Time elapsed: 0.169 s
% 0.21/0.60  % (13222)------------------------------
% 0.21/0.60  % (13222)------------------------------
% 0.21/0.60  % (13213)Success in time 0.229 s
%------------------------------------------------------------------------------
