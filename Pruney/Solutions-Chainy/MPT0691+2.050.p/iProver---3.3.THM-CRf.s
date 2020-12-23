%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:47 EST 2020

% Result     : Theorem 19.83s
% Output     : CNFRefutation 19.83s
% Verified   : 
% Statistics : Number of formulae       :  176 (1581 expanded)
%              Number of clauses        :   84 ( 283 expanded)
%              Number of leaves         :   28 ( 421 expanded)
%              Depth                    :   25
%              Number of atoms          :  300 (2310 expanded)
%              Number of equality atoms :  174 (1499 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f90])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f91])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f92])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f93])).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f94])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f60,f95])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f96])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f54,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f54,f95])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f96])).

fof(f18,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f26,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f30,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f52,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f52])).

fof(f88,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f87,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f86,f95])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f58,f96])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1055,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1050,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5048,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_1055,c_1050])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1054,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4396,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1055,c_1054])).

cnf(c_4410,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4396,c_0])).

cnf(c_5068,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5048,c_0,c_4410])).

cnf(c_12,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1047,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1042,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1957,plain,
    ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1047,c_1042])).

cnf(c_20,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_21,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1960,plain,
    ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1957,c_20,c_21])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1035,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1048,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1052,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3464,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_1052])).

cnf(c_22581,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,X0),k2_xboole_0(k1_relat_1(sK1),X0)) = k2_xboole_0(k1_relat_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_1035,c_3464])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1041,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3578,plain,
    ( k2_xboole_0(k10_relat_1(k6_relat_1(X0),X1),k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1047,c_1041])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1049,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_30036,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3578,c_1049])).

cnf(c_32461,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),k2_xboole_0(sK0,X1)),k10_relat_1(k6_relat_1(X0),k2_xboole_0(k1_relat_1(sK1),X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22581,c_30036])).

cnf(c_32958,plain,
    ( r1_tarski(k2_xboole_0(sK0,X0),k10_relat_1(k6_relat_1(k2_xboole_0(sK0,X0)),k2_xboole_0(k1_relat_1(sK1),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1960,c_32461])).

cnf(c_33525,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_xboole_0),k10_relat_1(k6_relat_1(k2_xboole_0(sK0,k1_xboole_0)),k1_relat_1(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5068,c_32958])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1034,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1040,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3138,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1040])).

cnf(c_17567,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) ),
    inference(superposition,[status(thm)],[c_1034,c_3138])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1038,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2096,plain,
    ( k5_relat_1(k6_relat_1(X0),sK1) = k7_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1034,c_1038])).

cnf(c_17568,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_17567,c_2096])).

cnf(c_33605,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,k2_xboole_0(sK0,k1_xboole_0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_33525,c_5068,c_17568])).

cnf(c_33606,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_33605,c_5068])).

cnf(c_34454,plain,
    ( k2_xboole_0(sK0,k5_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),k1_setfam_1(k6_enumset1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),sK0)))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_33606,c_1050])).

cnf(c_22,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1039,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2488,plain,
    ( k2_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1) = X1
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_1052])).

cnf(c_11605,plain,
    ( k2_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1034,c_2488])).

cnf(c_11617,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11605,c_1049])).

cnf(c_11771,plain,
    ( k5_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k1_setfam_1(k6_enumset1(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11617,c_1054])).

cnf(c_34464,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_34454,c_5068,c_11771])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1046,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1958,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1042])).

cnf(c_8551,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1034,c_1958])).

cnf(c_24,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1037,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1462,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_1034,c_1037])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1053,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4349,plain,
    ( k5_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X0),X1)) != k1_xboole_0
    | r1_tarski(X0,k10_relat_1(sK1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_1053])).

cnf(c_8901,plain,
    ( k5_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) != k1_xboole_0
    | r1_tarski(X0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8551,c_4349])).

cnf(c_71706,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_34464,c_8901])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1045,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2338,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k2_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1045])).

cnf(c_11293,plain,
    ( k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1034,c_2338])).

cnf(c_34617,plain,
    ( k9_relat_1(k7_relat_1(sK1,sK0),sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_34464,c_11293])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1044,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4220,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),X1) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1055,c_1044])).

cnf(c_22247,plain,
    ( k9_relat_1(k7_relat_1(sK1,X0),X0) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1034,c_4220])).

cnf(c_34626,plain,
    ( k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_34617,c_22247])).

cnf(c_71721,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_71706,c_34626])).

cnf(c_71722,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_71721,c_4410])).

cnf(c_71723,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_71722])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_30,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71723,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.83/3.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.83/3.06  
% 19.83/3.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.83/3.06  
% 19.83/3.06  ------  iProver source info
% 19.83/3.06  
% 19.83/3.06  git: date: 2020-06-30 10:37:57 +0100
% 19.83/3.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.83/3.06  git: non_committed_changes: false
% 19.83/3.06  git: last_make_outside_of_git: false
% 19.83/3.06  
% 19.83/3.06  ------ 
% 19.83/3.06  
% 19.83/3.06  ------ Input Options
% 19.83/3.06  
% 19.83/3.06  --out_options                           all
% 19.83/3.06  --tptp_safe_out                         true
% 19.83/3.06  --problem_path                          ""
% 19.83/3.06  --include_path                          ""
% 19.83/3.06  --clausifier                            res/vclausify_rel
% 19.83/3.06  --clausifier_options                    ""
% 19.83/3.06  --stdin                                 false
% 19.83/3.06  --stats_out                             all
% 19.83/3.06  
% 19.83/3.06  ------ General Options
% 19.83/3.06  
% 19.83/3.06  --fof                                   false
% 19.83/3.06  --time_out_real                         305.
% 19.83/3.06  --time_out_virtual                      -1.
% 19.83/3.06  --symbol_type_check                     false
% 19.83/3.06  --clausify_out                          false
% 19.83/3.06  --sig_cnt_out                           false
% 19.83/3.06  --trig_cnt_out                          false
% 19.83/3.06  --trig_cnt_out_tolerance                1.
% 19.83/3.06  --trig_cnt_out_sk_spl                   false
% 19.83/3.06  --abstr_cl_out                          false
% 19.83/3.06  
% 19.83/3.06  ------ Global Options
% 19.83/3.06  
% 19.83/3.06  --schedule                              default
% 19.83/3.06  --add_important_lit                     false
% 19.83/3.06  --prop_solver_per_cl                    1000
% 19.83/3.06  --min_unsat_core                        false
% 19.83/3.06  --soft_assumptions                      false
% 19.83/3.06  --soft_lemma_size                       3
% 19.83/3.06  --prop_impl_unit_size                   0
% 19.83/3.06  --prop_impl_unit                        []
% 19.83/3.06  --share_sel_clauses                     true
% 19.83/3.06  --reset_solvers                         false
% 19.83/3.06  --bc_imp_inh                            [conj_cone]
% 19.83/3.06  --conj_cone_tolerance                   3.
% 19.83/3.06  --extra_neg_conj                        none
% 19.83/3.06  --large_theory_mode                     true
% 19.83/3.06  --prolific_symb_bound                   200
% 19.83/3.06  --lt_threshold                          2000
% 19.83/3.06  --clause_weak_htbl                      true
% 19.83/3.06  --gc_record_bc_elim                     false
% 19.83/3.06  
% 19.83/3.06  ------ Preprocessing Options
% 19.83/3.06  
% 19.83/3.06  --preprocessing_flag                    true
% 19.83/3.06  --time_out_prep_mult                    0.1
% 19.83/3.06  --splitting_mode                        input
% 19.83/3.06  --splitting_grd                         true
% 19.83/3.06  --splitting_cvd                         false
% 19.83/3.06  --splitting_cvd_svl                     false
% 19.83/3.06  --splitting_nvd                         32
% 19.83/3.06  --sub_typing                            true
% 19.83/3.06  --prep_gs_sim                           true
% 19.83/3.06  --prep_unflatten                        true
% 19.83/3.06  --prep_res_sim                          true
% 19.83/3.06  --prep_upred                            true
% 19.83/3.06  --prep_sem_filter                       exhaustive
% 19.83/3.06  --prep_sem_filter_out                   false
% 19.83/3.06  --pred_elim                             true
% 19.83/3.06  --res_sim_input                         true
% 19.83/3.06  --eq_ax_congr_red                       true
% 19.83/3.06  --pure_diseq_elim                       true
% 19.83/3.06  --brand_transform                       false
% 19.83/3.06  --non_eq_to_eq                          false
% 19.83/3.06  --prep_def_merge                        true
% 19.83/3.06  --prep_def_merge_prop_impl              false
% 19.83/3.06  --prep_def_merge_mbd                    true
% 19.83/3.06  --prep_def_merge_tr_red                 false
% 19.83/3.06  --prep_def_merge_tr_cl                  false
% 19.83/3.06  --smt_preprocessing                     true
% 19.83/3.06  --smt_ac_axioms                         fast
% 19.83/3.06  --preprocessed_out                      false
% 19.83/3.06  --preprocessed_stats                    false
% 19.83/3.06  
% 19.83/3.06  ------ Abstraction refinement Options
% 19.83/3.06  
% 19.83/3.06  --abstr_ref                             []
% 19.83/3.06  --abstr_ref_prep                        false
% 19.83/3.06  --abstr_ref_until_sat                   false
% 19.83/3.06  --abstr_ref_sig_restrict                funpre
% 19.83/3.06  --abstr_ref_af_restrict_to_split_sk     false
% 19.83/3.06  --abstr_ref_under                       []
% 19.83/3.06  
% 19.83/3.06  ------ SAT Options
% 19.83/3.06  
% 19.83/3.06  --sat_mode                              false
% 19.83/3.06  --sat_fm_restart_options                ""
% 19.83/3.06  --sat_gr_def                            false
% 19.83/3.06  --sat_epr_types                         true
% 19.83/3.06  --sat_non_cyclic_types                  false
% 19.83/3.06  --sat_finite_models                     false
% 19.83/3.06  --sat_fm_lemmas                         false
% 19.83/3.06  --sat_fm_prep                           false
% 19.83/3.06  --sat_fm_uc_incr                        true
% 19.83/3.06  --sat_out_model                         small
% 19.83/3.06  --sat_out_clauses                       false
% 19.83/3.06  
% 19.83/3.06  ------ QBF Options
% 19.83/3.06  
% 19.83/3.06  --qbf_mode                              false
% 19.83/3.06  --qbf_elim_univ                         false
% 19.83/3.06  --qbf_dom_inst                          none
% 19.83/3.06  --qbf_dom_pre_inst                      false
% 19.83/3.06  --qbf_sk_in                             false
% 19.83/3.06  --qbf_pred_elim                         true
% 19.83/3.06  --qbf_split                             512
% 19.83/3.06  
% 19.83/3.06  ------ BMC1 Options
% 19.83/3.06  
% 19.83/3.06  --bmc1_incremental                      false
% 19.83/3.06  --bmc1_axioms                           reachable_all
% 19.83/3.06  --bmc1_min_bound                        0
% 19.83/3.06  --bmc1_max_bound                        -1
% 19.83/3.06  --bmc1_max_bound_default                -1
% 19.83/3.06  --bmc1_symbol_reachability              true
% 19.83/3.06  --bmc1_property_lemmas                  false
% 19.83/3.06  --bmc1_k_induction                      false
% 19.83/3.06  --bmc1_non_equiv_states                 false
% 19.83/3.06  --bmc1_deadlock                         false
% 19.83/3.06  --bmc1_ucm                              false
% 19.83/3.06  --bmc1_add_unsat_core                   none
% 19.83/3.06  --bmc1_unsat_core_children              false
% 19.83/3.06  --bmc1_unsat_core_extrapolate_axioms    false
% 19.83/3.06  --bmc1_out_stat                         full
% 19.83/3.06  --bmc1_ground_init                      false
% 19.83/3.06  --bmc1_pre_inst_next_state              false
% 19.83/3.06  --bmc1_pre_inst_state                   false
% 19.83/3.06  --bmc1_pre_inst_reach_state             false
% 19.83/3.06  --bmc1_out_unsat_core                   false
% 19.83/3.06  --bmc1_aig_witness_out                  false
% 19.83/3.06  --bmc1_verbose                          false
% 19.83/3.06  --bmc1_dump_clauses_tptp                false
% 19.83/3.06  --bmc1_dump_unsat_core_tptp             false
% 19.83/3.06  --bmc1_dump_file                        -
% 19.83/3.06  --bmc1_ucm_expand_uc_limit              128
% 19.83/3.06  --bmc1_ucm_n_expand_iterations          6
% 19.83/3.06  --bmc1_ucm_extend_mode                  1
% 19.83/3.06  --bmc1_ucm_init_mode                    2
% 19.83/3.06  --bmc1_ucm_cone_mode                    none
% 19.83/3.06  --bmc1_ucm_reduced_relation_type        0
% 19.83/3.06  --bmc1_ucm_relax_model                  4
% 19.83/3.06  --bmc1_ucm_full_tr_after_sat            true
% 19.83/3.06  --bmc1_ucm_expand_neg_assumptions       false
% 19.83/3.06  --bmc1_ucm_layered_model                none
% 19.83/3.06  --bmc1_ucm_max_lemma_size               10
% 19.83/3.06  
% 19.83/3.06  ------ AIG Options
% 19.83/3.06  
% 19.83/3.06  --aig_mode                              false
% 19.83/3.06  
% 19.83/3.06  ------ Instantiation Options
% 19.83/3.06  
% 19.83/3.06  --instantiation_flag                    true
% 19.83/3.06  --inst_sos_flag                         true
% 19.83/3.06  --inst_sos_phase                        true
% 19.83/3.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.83/3.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.83/3.06  --inst_lit_sel_side                     num_symb
% 19.83/3.06  --inst_solver_per_active                1400
% 19.83/3.06  --inst_solver_calls_frac                1.
% 19.83/3.06  --inst_passive_queue_type               priority_queues
% 19.83/3.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.83/3.06  --inst_passive_queues_freq              [25;2]
% 19.83/3.06  --inst_dismatching                      true
% 19.83/3.06  --inst_eager_unprocessed_to_passive     true
% 19.83/3.06  --inst_prop_sim_given                   true
% 19.83/3.06  --inst_prop_sim_new                     false
% 19.83/3.06  --inst_subs_new                         false
% 19.83/3.06  --inst_eq_res_simp                      false
% 19.83/3.06  --inst_subs_given                       false
% 19.83/3.06  --inst_orphan_elimination               true
% 19.83/3.06  --inst_learning_loop_flag               true
% 19.83/3.06  --inst_learning_start                   3000
% 19.83/3.06  --inst_learning_factor                  2
% 19.83/3.06  --inst_start_prop_sim_after_learn       3
% 19.83/3.06  --inst_sel_renew                        solver
% 19.83/3.06  --inst_lit_activity_flag                true
% 19.83/3.06  --inst_restr_to_given                   false
% 19.83/3.06  --inst_activity_threshold               500
% 19.83/3.06  --inst_out_proof                        true
% 19.83/3.06  
% 19.83/3.06  ------ Resolution Options
% 19.83/3.06  
% 19.83/3.06  --resolution_flag                       true
% 19.83/3.06  --res_lit_sel                           adaptive
% 19.83/3.06  --res_lit_sel_side                      none
% 19.83/3.06  --res_ordering                          kbo
% 19.83/3.06  --res_to_prop_solver                    active
% 19.83/3.06  --res_prop_simpl_new                    false
% 19.83/3.06  --res_prop_simpl_given                  true
% 19.83/3.06  --res_passive_queue_type                priority_queues
% 19.83/3.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.83/3.06  --res_passive_queues_freq               [15;5]
% 19.83/3.06  --res_forward_subs                      full
% 19.83/3.06  --res_backward_subs                     full
% 19.83/3.06  --res_forward_subs_resolution           true
% 19.83/3.06  --res_backward_subs_resolution          true
% 19.83/3.06  --res_orphan_elimination                true
% 19.83/3.06  --res_time_limit                        2.
% 19.83/3.06  --res_out_proof                         true
% 19.83/3.06  
% 19.83/3.06  ------ Superposition Options
% 19.83/3.06  
% 19.83/3.06  --superposition_flag                    true
% 19.83/3.06  --sup_passive_queue_type                priority_queues
% 19.83/3.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.83/3.06  --sup_passive_queues_freq               [8;1;4]
% 19.83/3.06  --demod_completeness_check              fast
% 19.83/3.06  --demod_use_ground                      true
% 19.83/3.06  --sup_to_prop_solver                    passive
% 19.83/3.06  --sup_prop_simpl_new                    true
% 19.83/3.06  --sup_prop_simpl_given                  true
% 19.83/3.06  --sup_fun_splitting                     true
% 19.83/3.06  --sup_smt_interval                      50000
% 19.83/3.06  
% 19.83/3.06  ------ Superposition Simplification Setup
% 19.83/3.06  
% 19.83/3.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.83/3.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.83/3.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.83/3.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.83/3.06  --sup_full_triv                         [TrivRules;PropSubs]
% 19.83/3.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.83/3.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.83/3.06  --sup_immed_triv                        [TrivRules]
% 19.83/3.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.06  --sup_immed_bw_main                     []
% 19.83/3.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.83/3.06  --sup_input_triv                        [Unflattening;TrivRules]
% 19.83/3.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.06  --sup_input_bw                          []
% 19.83/3.06  
% 19.83/3.06  ------ Combination Options
% 19.83/3.06  
% 19.83/3.06  --comb_res_mult                         3
% 19.83/3.06  --comb_sup_mult                         2
% 19.83/3.06  --comb_inst_mult                        10
% 19.83/3.06  
% 19.83/3.06  ------ Debug Options
% 19.83/3.06  
% 19.83/3.06  --dbg_backtrace                         false
% 19.83/3.06  --dbg_dump_prop_clauses                 false
% 19.83/3.06  --dbg_dump_prop_clauses_file            -
% 19.83/3.06  --dbg_out_stat                          false
% 19.83/3.06  ------ Parsing...
% 19.83/3.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.83/3.06  
% 19.83/3.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.83/3.06  
% 19.83/3.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.83/3.06  
% 19.83/3.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.83/3.06  ------ Proving...
% 19.83/3.06  ------ Problem Properties 
% 19.83/3.06  
% 19.83/3.06  
% 19.83/3.06  clauses                                 27
% 19.83/3.06  conjectures                             3
% 19.83/3.06  EPR                                     3
% 19.83/3.06  Horn                                    27
% 19.83/3.06  unary                                   10
% 19.83/3.06  binary                                  14
% 19.83/3.06  lits                                    47
% 19.83/3.06  lits eq                                 16
% 19.83/3.06  fd_pure                                 0
% 19.83/3.06  fd_pseudo                               0
% 19.83/3.06  fd_cond                                 0
% 19.83/3.06  fd_pseudo_cond                          1
% 19.83/3.06  AC symbols                              0
% 19.83/3.06  
% 19.83/3.06  ------ Schedule dynamic 5 is on 
% 19.83/3.06  
% 19.83/3.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.83/3.06  
% 19.83/3.06  
% 19.83/3.06  ------ 
% 19.83/3.06  Current options:
% 19.83/3.06  ------ 
% 19.83/3.06  
% 19.83/3.06  ------ Input Options
% 19.83/3.06  
% 19.83/3.06  --out_options                           all
% 19.83/3.06  --tptp_safe_out                         true
% 19.83/3.06  --problem_path                          ""
% 19.83/3.06  --include_path                          ""
% 19.83/3.06  --clausifier                            res/vclausify_rel
% 19.83/3.06  --clausifier_options                    ""
% 19.83/3.06  --stdin                                 false
% 19.83/3.06  --stats_out                             all
% 19.83/3.06  
% 19.83/3.06  ------ General Options
% 19.83/3.06  
% 19.83/3.06  --fof                                   false
% 19.83/3.06  --time_out_real                         305.
% 19.83/3.06  --time_out_virtual                      -1.
% 19.83/3.06  --symbol_type_check                     false
% 19.83/3.06  --clausify_out                          false
% 19.83/3.06  --sig_cnt_out                           false
% 19.83/3.06  --trig_cnt_out                          false
% 19.83/3.06  --trig_cnt_out_tolerance                1.
% 19.83/3.06  --trig_cnt_out_sk_spl                   false
% 19.83/3.06  --abstr_cl_out                          false
% 19.83/3.06  
% 19.83/3.06  ------ Global Options
% 19.83/3.06  
% 19.83/3.06  --schedule                              default
% 19.83/3.06  --add_important_lit                     false
% 19.83/3.06  --prop_solver_per_cl                    1000
% 19.83/3.06  --min_unsat_core                        false
% 19.83/3.06  --soft_assumptions                      false
% 19.83/3.06  --soft_lemma_size                       3
% 19.83/3.06  --prop_impl_unit_size                   0
% 19.83/3.06  --prop_impl_unit                        []
% 19.83/3.06  --share_sel_clauses                     true
% 19.83/3.06  --reset_solvers                         false
% 19.83/3.06  --bc_imp_inh                            [conj_cone]
% 19.83/3.06  --conj_cone_tolerance                   3.
% 19.83/3.06  --extra_neg_conj                        none
% 19.83/3.06  --large_theory_mode                     true
% 19.83/3.06  --prolific_symb_bound                   200
% 19.83/3.06  --lt_threshold                          2000
% 19.83/3.06  --clause_weak_htbl                      true
% 19.83/3.06  --gc_record_bc_elim                     false
% 19.83/3.06  
% 19.83/3.06  ------ Preprocessing Options
% 19.83/3.06  
% 19.83/3.06  --preprocessing_flag                    true
% 19.83/3.06  --time_out_prep_mult                    0.1
% 19.83/3.06  --splitting_mode                        input
% 19.83/3.06  --splitting_grd                         true
% 19.83/3.06  --splitting_cvd                         false
% 19.83/3.06  --splitting_cvd_svl                     false
% 19.83/3.06  --splitting_nvd                         32
% 19.83/3.06  --sub_typing                            true
% 19.83/3.06  --prep_gs_sim                           true
% 19.83/3.06  --prep_unflatten                        true
% 19.83/3.06  --prep_res_sim                          true
% 19.83/3.06  --prep_upred                            true
% 19.83/3.06  --prep_sem_filter                       exhaustive
% 19.83/3.06  --prep_sem_filter_out                   false
% 19.83/3.06  --pred_elim                             true
% 19.83/3.06  --res_sim_input                         true
% 19.83/3.06  --eq_ax_congr_red                       true
% 19.83/3.06  --pure_diseq_elim                       true
% 19.83/3.06  --brand_transform                       false
% 19.83/3.06  --non_eq_to_eq                          false
% 19.83/3.06  --prep_def_merge                        true
% 19.83/3.06  --prep_def_merge_prop_impl              false
% 19.83/3.06  --prep_def_merge_mbd                    true
% 19.83/3.06  --prep_def_merge_tr_red                 false
% 19.83/3.06  --prep_def_merge_tr_cl                  false
% 19.83/3.06  --smt_preprocessing                     true
% 19.83/3.06  --smt_ac_axioms                         fast
% 19.83/3.06  --preprocessed_out                      false
% 19.83/3.06  --preprocessed_stats                    false
% 19.83/3.06  
% 19.83/3.06  ------ Abstraction refinement Options
% 19.83/3.06  
% 19.83/3.06  --abstr_ref                             []
% 19.83/3.06  --abstr_ref_prep                        false
% 19.83/3.06  --abstr_ref_until_sat                   false
% 19.83/3.06  --abstr_ref_sig_restrict                funpre
% 19.83/3.06  --abstr_ref_af_restrict_to_split_sk     false
% 19.83/3.06  --abstr_ref_under                       []
% 19.83/3.06  
% 19.83/3.06  ------ SAT Options
% 19.83/3.06  
% 19.83/3.06  --sat_mode                              false
% 19.83/3.06  --sat_fm_restart_options                ""
% 19.83/3.06  --sat_gr_def                            false
% 19.83/3.06  --sat_epr_types                         true
% 19.83/3.06  --sat_non_cyclic_types                  false
% 19.83/3.06  --sat_finite_models                     false
% 19.83/3.06  --sat_fm_lemmas                         false
% 19.83/3.06  --sat_fm_prep                           false
% 19.83/3.06  --sat_fm_uc_incr                        true
% 19.83/3.06  --sat_out_model                         small
% 19.83/3.06  --sat_out_clauses                       false
% 19.83/3.06  
% 19.83/3.06  ------ QBF Options
% 19.83/3.06  
% 19.83/3.06  --qbf_mode                              false
% 19.83/3.06  --qbf_elim_univ                         false
% 19.83/3.06  --qbf_dom_inst                          none
% 19.83/3.06  --qbf_dom_pre_inst                      false
% 19.83/3.06  --qbf_sk_in                             false
% 19.83/3.06  --qbf_pred_elim                         true
% 19.83/3.06  --qbf_split                             512
% 19.83/3.06  
% 19.83/3.06  ------ BMC1 Options
% 19.83/3.06  
% 19.83/3.06  --bmc1_incremental                      false
% 19.83/3.06  --bmc1_axioms                           reachable_all
% 19.83/3.06  --bmc1_min_bound                        0
% 19.83/3.06  --bmc1_max_bound                        -1
% 19.83/3.06  --bmc1_max_bound_default                -1
% 19.83/3.06  --bmc1_symbol_reachability              true
% 19.83/3.06  --bmc1_property_lemmas                  false
% 19.83/3.06  --bmc1_k_induction                      false
% 19.83/3.06  --bmc1_non_equiv_states                 false
% 19.83/3.06  --bmc1_deadlock                         false
% 19.83/3.06  --bmc1_ucm                              false
% 19.83/3.06  --bmc1_add_unsat_core                   none
% 19.83/3.06  --bmc1_unsat_core_children              false
% 19.83/3.06  --bmc1_unsat_core_extrapolate_axioms    false
% 19.83/3.06  --bmc1_out_stat                         full
% 19.83/3.06  --bmc1_ground_init                      false
% 19.83/3.06  --bmc1_pre_inst_next_state              false
% 19.83/3.06  --bmc1_pre_inst_state                   false
% 19.83/3.06  --bmc1_pre_inst_reach_state             false
% 19.83/3.06  --bmc1_out_unsat_core                   false
% 19.83/3.06  --bmc1_aig_witness_out                  false
% 19.83/3.06  --bmc1_verbose                          false
% 19.83/3.06  --bmc1_dump_clauses_tptp                false
% 19.83/3.06  --bmc1_dump_unsat_core_tptp             false
% 19.83/3.06  --bmc1_dump_file                        -
% 19.83/3.06  --bmc1_ucm_expand_uc_limit              128
% 19.83/3.06  --bmc1_ucm_n_expand_iterations          6
% 19.83/3.06  --bmc1_ucm_extend_mode                  1
% 19.83/3.06  --bmc1_ucm_init_mode                    2
% 19.83/3.06  --bmc1_ucm_cone_mode                    none
% 19.83/3.06  --bmc1_ucm_reduced_relation_type        0
% 19.83/3.06  --bmc1_ucm_relax_model                  4
% 19.83/3.06  --bmc1_ucm_full_tr_after_sat            true
% 19.83/3.06  --bmc1_ucm_expand_neg_assumptions       false
% 19.83/3.06  --bmc1_ucm_layered_model                none
% 19.83/3.06  --bmc1_ucm_max_lemma_size               10
% 19.83/3.06  
% 19.83/3.06  ------ AIG Options
% 19.83/3.06  
% 19.83/3.06  --aig_mode                              false
% 19.83/3.06  
% 19.83/3.06  ------ Instantiation Options
% 19.83/3.06  
% 19.83/3.06  --instantiation_flag                    true
% 19.83/3.06  --inst_sos_flag                         true
% 19.83/3.06  --inst_sos_phase                        true
% 19.83/3.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.83/3.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.83/3.06  --inst_lit_sel_side                     none
% 19.83/3.06  --inst_solver_per_active                1400
% 19.83/3.06  --inst_solver_calls_frac                1.
% 19.83/3.06  --inst_passive_queue_type               priority_queues
% 19.83/3.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.83/3.06  --inst_passive_queues_freq              [25;2]
% 19.83/3.06  --inst_dismatching                      true
% 19.83/3.06  --inst_eager_unprocessed_to_passive     true
% 19.83/3.06  --inst_prop_sim_given                   true
% 19.83/3.06  --inst_prop_sim_new                     false
% 19.83/3.06  --inst_subs_new                         false
% 19.83/3.06  --inst_eq_res_simp                      false
% 19.83/3.06  --inst_subs_given                       false
% 19.83/3.06  --inst_orphan_elimination               true
% 19.83/3.06  --inst_learning_loop_flag               true
% 19.83/3.06  --inst_learning_start                   3000
% 19.83/3.06  --inst_learning_factor                  2
% 19.83/3.06  --inst_start_prop_sim_after_learn       3
% 19.83/3.06  --inst_sel_renew                        solver
% 19.83/3.06  --inst_lit_activity_flag                true
% 19.83/3.06  --inst_restr_to_given                   false
% 19.83/3.06  --inst_activity_threshold               500
% 19.83/3.06  --inst_out_proof                        true
% 19.83/3.06  
% 19.83/3.06  ------ Resolution Options
% 19.83/3.06  
% 19.83/3.06  --resolution_flag                       false
% 19.83/3.06  --res_lit_sel                           adaptive
% 19.83/3.06  --res_lit_sel_side                      none
% 19.83/3.06  --res_ordering                          kbo
% 19.83/3.06  --res_to_prop_solver                    active
% 19.83/3.06  --res_prop_simpl_new                    false
% 19.83/3.06  --res_prop_simpl_given                  true
% 19.83/3.06  --res_passive_queue_type                priority_queues
% 19.83/3.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.83/3.06  --res_passive_queues_freq               [15;5]
% 19.83/3.06  --res_forward_subs                      full
% 19.83/3.06  --res_backward_subs                     full
% 19.83/3.06  --res_forward_subs_resolution           true
% 19.83/3.06  --res_backward_subs_resolution          true
% 19.83/3.06  --res_orphan_elimination                true
% 19.83/3.06  --res_time_limit                        2.
% 19.83/3.06  --res_out_proof                         true
% 19.83/3.06  
% 19.83/3.06  ------ Superposition Options
% 19.83/3.06  
% 19.83/3.06  --superposition_flag                    true
% 19.83/3.06  --sup_passive_queue_type                priority_queues
% 19.83/3.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.83/3.06  --sup_passive_queues_freq               [8;1;4]
% 19.83/3.06  --demod_completeness_check              fast
% 19.83/3.06  --demod_use_ground                      true
% 19.83/3.06  --sup_to_prop_solver                    passive
% 19.83/3.06  --sup_prop_simpl_new                    true
% 19.83/3.06  --sup_prop_simpl_given                  true
% 19.83/3.06  --sup_fun_splitting                     true
% 19.83/3.06  --sup_smt_interval                      50000
% 19.83/3.06  
% 19.83/3.06  ------ Superposition Simplification Setup
% 19.83/3.06  
% 19.83/3.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.83/3.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.83/3.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.83/3.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.83/3.06  --sup_full_triv                         [TrivRules;PropSubs]
% 19.83/3.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.83/3.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.83/3.06  --sup_immed_triv                        [TrivRules]
% 19.83/3.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.06  --sup_immed_bw_main                     []
% 19.83/3.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.83/3.06  --sup_input_triv                        [Unflattening;TrivRules]
% 19.83/3.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.06  --sup_input_bw                          []
% 19.83/3.06  
% 19.83/3.06  ------ Combination Options
% 19.83/3.06  
% 19.83/3.06  --comb_res_mult                         3
% 19.83/3.06  --comb_sup_mult                         2
% 19.83/3.06  --comb_inst_mult                        10
% 19.83/3.06  
% 19.83/3.06  ------ Debug Options
% 19.83/3.06  
% 19.83/3.06  --dbg_backtrace                         false
% 19.83/3.06  --dbg_dump_prop_clauses                 false
% 19.83/3.06  --dbg_dump_prop_clauses_file            -
% 19.83/3.06  --dbg_out_stat                          false
% 19.83/3.06  
% 19.83/3.06  
% 19.83/3.06  
% 19.83/3.06  
% 19.83/3.06  ------ Proving...
% 19.83/3.06  
% 19.83/3.06  
% 19.83/3.06  % SZS status Theorem for theBenchmark.p
% 19.83/3.06  
% 19.83/3.06  % SZS output start CNFRefutation for theBenchmark.p
% 19.83/3.06  
% 19.83/3.06  fof(f2,axiom,(
% 19.83/3.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f49,plain,(
% 19.83/3.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.83/3.06    inference(nnf_transformation,[],[f2])).
% 19.83/3.06  
% 19.83/3.06  fof(f50,plain,(
% 19.83/3.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.83/3.06    inference(flattening,[],[f49])).
% 19.83/3.06  
% 19.83/3.06  fof(f55,plain,(
% 19.83/3.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.83/3.06    inference(cnf_transformation,[],[f50])).
% 19.83/3.06  
% 19.83/3.06  fof(f105,plain,(
% 19.83/3.06    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.83/3.06    inference(equality_resolution,[],[f55])).
% 19.83/3.06  
% 19.83/3.06  fof(f8,axiom,(
% 19.83/3.06    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f35,plain,(
% 19.83/3.06    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 19.83/3.06    inference(ennf_transformation,[],[f8])).
% 19.83/3.06  
% 19.83/3.06  fof(f64,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f35])).
% 19.83/3.06  
% 19.83/3.06  fof(f4,axiom,(
% 19.83/3.06    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f60,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 19.83/3.06    inference(cnf_transformation,[],[f4])).
% 19.83/3.06  
% 19.83/3.06  fof(f17,axiom,(
% 19.83/3.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f73,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.83/3.06    inference(cnf_transformation,[],[f17])).
% 19.83/3.06  
% 19.83/3.06  fof(f11,axiom,(
% 19.83/3.06    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f67,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f11])).
% 19.83/3.06  
% 19.83/3.06  fof(f12,axiom,(
% 19.83/3.06    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f68,plain,(
% 19.83/3.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f12])).
% 19.83/3.06  
% 19.83/3.06  fof(f13,axiom,(
% 19.83/3.06    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f69,plain,(
% 19.83/3.06    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f13])).
% 19.83/3.06  
% 19.83/3.06  fof(f14,axiom,(
% 19.83/3.06    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f70,plain,(
% 19.83/3.06    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f14])).
% 19.83/3.06  
% 19.83/3.06  fof(f15,axiom,(
% 19.83/3.06    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f71,plain,(
% 19.83/3.06    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f15])).
% 19.83/3.06  
% 19.83/3.06  fof(f16,axiom,(
% 19.83/3.06    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f72,plain,(
% 19.83/3.06    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f16])).
% 19.83/3.06  
% 19.83/3.06  fof(f90,plain,(
% 19.83/3.06    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 19.83/3.06    inference(definition_unfolding,[],[f71,f72])).
% 19.83/3.06  
% 19.83/3.06  fof(f91,plain,(
% 19.83/3.06    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 19.83/3.06    inference(definition_unfolding,[],[f70,f90])).
% 19.83/3.06  
% 19.83/3.06  fof(f92,plain,(
% 19.83/3.06    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 19.83/3.06    inference(definition_unfolding,[],[f69,f91])).
% 19.83/3.06  
% 19.83/3.06  fof(f93,plain,(
% 19.83/3.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 19.83/3.06    inference(definition_unfolding,[],[f68,f92])).
% 19.83/3.06  
% 19.83/3.06  fof(f94,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 19.83/3.06    inference(definition_unfolding,[],[f67,f93])).
% 19.83/3.06  
% 19.83/3.06  fof(f95,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 19.83/3.06    inference(definition_unfolding,[],[f73,f94])).
% 19.83/3.06  
% 19.83/3.06  fof(f96,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 19.83/3.06    inference(definition_unfolding,[],[f60,f95])).
% 19.83/3.06  
% 19.83/3.06  fof(f102,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1 | ~r1_tarski(X0,X1)) )),
% 19.83/3.06    inference(definition_unfolding,[],[f64,f96])).
% 19.83/3.06  
% 19.83/3.06  fof(f1,axiom,(
% 19.83/3.06    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f32,plain,(
% 19.83/3.06    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 19.83/3.06    inference(rectify,[],[f1])).
% 19.83/3.06  
% 19.83/3.06  fof(f54,plain,(
% 19.83/3.06    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 19.83/3.06    inference(cnf_transformation,[],[f32])).
% 19.83/3.06  
% 19.83/3.06  fof(f97,plain,(
% 19.83/3.06    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 19.83/3.06    inference(definition_unfolding,[],[f54,f95])).
% 19.83/3.06  
% 19.83/3.06  fof(f3,axiom,(
% 19.83/3.06    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f51,plain,(
% 19.83/3.06    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 19.83/3.06    inference(nnf_transformation,[],[f3])).
% 19.83/3.06  
% 19.83/3.06  fof(f59,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f51])).
% 19.83/3.06  
% 19.83/3.06  fof(f98,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 19.83/3.06    inference(definition_unfolding,[],[f59,f96])).
% 19.83/3.06  
% 19.83/3.06  fof(f18,axiom,(
% 19.83/3.06    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f74,plain,(
% 19.83/3.06    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 19.83/3.06    inference(cnf_transformation,[],[f18])).
% 19.83/3.06  
% 19.83/3.06  fof(f23,axiom,(
% 19.83/3.06    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f41,plain,(
% 19.83/3.06    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 19.83/3.06    inference(ennf_transformation,[],[f23])).
% 19.83/3.06  
% 19.83/3.06  fof(f79,plain,(
% 19.83/3.06    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f41])).
% 19.83/3.06  
% 19.83/3.06  fof(f26,axiom,(
% 19.83/3.06    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f83,plain,(
% 19.83/3.06    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 19.83/3.06    inference(cnf_transformation,[],[f26])).
% 19.83/3.06  
% 19.83/3.06  fof(f82,plain,(
% 19.83/3.06    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 19.83/3.06    inference(cnf_transformation,[],[f26])).
% 19.83/3.06  
% 19.83/3.06  fof(f30,conjecture,(
% 19.83/3.06    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f31,negated_conjecture,(
% 19.83/3.06    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 19.83/3.06    inference(negated_conjecture,[],[f30])).
% 19.83/3.06  
% 19.83/3.06  fof(f47,plain,(
% 19.83/3.06    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 19.83/3.06    inference(ennf_transformation,[],[f31])).
% 19.83/3.06  
% 19.83/3.06  fof(f48,plain,(
% 19.83/3.06    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 19.83/3.06    inference(flattening,[],[f47])).
% 19.83/3.06  
% 19.83/3.06  fof(f52,plain,(
% 19.83/3.06    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 19.83/3.06    introduced(choice_axiom,[])).
% 19.83/3.06  
% 19.83/3.06  fof(f53,plain,(
% 19.83/3.06    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 19.83/3.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f52])).
% 19.83/3.06  
% 19.83/3.06  fof(f88,plain,(
% 19.83/3.06    r1_tarski(sK0,k1_relat_1(sK1))),
% 19.83/3.06    inference(cnf_transformation,[],[f53])).
% 19.83/3.06  
% 19.83/3.06  fof(f10,axiom,(
% 19.83/3.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f36,plain,(
% 19.83/3.06    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 19.83/3.06    inference(ennf_transformation,[],[f10])).
% 19.83/3.06  
% 19.83/3.06  fof(f66,plain,(
% 19.83/3.06    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f36])).
% 19.83/3.06  
% 19.83/3.06  fof(f5,axiom,(
% 19.83/3.06    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f33,plain,(
% 19.83/3.06    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 19.83/3.06    inference(ennf_transformation,[],[f5])).
% 19.83/3.06  
% 19.83/3.06  fof(f61,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f33])).
% 19.83/3.06  
% 19.83/3.06  fof(f24,axiom,(
% 19.83/3.06    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f42,plain,(
% 19.83/3.06    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 19.83/3.06    inference(ennf_transformation,[],[f24])).
% 19.83/3.06  
% 19.83/3.06  fof(f80,plain,(
% 19.83/3.06    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f42])).
% 19.83/3.06  
% 19.83/3.06  fof(f9,axiom,(
% 19.83/3.06    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f65,plain,(
% 19.83/3.06    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 19.83/3.06    inference(cnf_transformation,[],[f9])).
% 19.83/3.06  
% 19.83/3.06  fof(f87,plain,(
% 19.83/3.06    v1_relat_1(sK1)),
% 19.83/3.06    inference(cnf_transformation,[],[f53])).
% 19.83/3.06  
% 19.83/3.06  fof(f25,axiom,(
% 19.83/3.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f43,plain,(
% 19.83/3.06    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.83/3.06    inference(ennf_transformation,[],[f25])).
% 19.83/3.06  
% 19.83/3.06  fof(f81,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f43])).
% 19.83/3.06  
% 19.83/3.06  fof(f28,axiom,(
% 19.83/3.06    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f45,plain,(
% 19.83/3.06    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 19.83/3.06    inference(ennf_transformation,[],[f28])).
% 19.83/3.06  
% 19.83/3.06  fof(f85,plain,(
% 19.83/3.06    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f45])).
% 19.83/3.06  
% 19.83/3.06  fof(f27,axiom,(
% 19.83/3.06    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f44,plain,(
% 19.83/3.06    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 19.83/3.06    inference(ennf_transformation,[],[f27])).
% 19.83/3.06  
% 19.83/3.06  fof(f84,plain,(
% 19.83/3.06    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f44])).
% 19.83/3.06  
% 19.83/3.06  fof(f19,axiom,(
% 19.83/3.06    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f37,plain,(
% 19.83/3.06    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 19.83/3.06    inference(ennf_transformation,[],[f19])).
% 19.83/3.06  
% 19.83/3.06  fof(f75,plain,(
% 19.83/3.06    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f37])).
% 19.83/3.06  
% 19.83/3.06  fof(f29,axiom,(
% 19.83/3.06    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f46,plain,(
% 19.83/3.06    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 19.83/3.06    inference(ennf_transformation,[],[f29])).
% 19.83/3.06  
% 19.83/3.06  fof(f86,plain,(
% 19.83/3.06    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f46])).
% 19.83/3.06  
% 19.83/3.06  fof(f103,plain,(
% 19.83/3.06    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 19.83/3.06    inference(definition_unfolding,[],[f86,f95])).
% 19.83/3.06  
% 19.83/3.06  fof(f58,plain,(
% 19.83/3.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 19.83/3.06    inference(cnf_transformation,[],[f51])).
% 19.83/3.06  
% 19.83/3.06  fof(f99,plain,(
% 19.83/3.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 19.83/3.06    inference(definition_unfolding,[],[f58,f96])).
% 19.83/3.06  
% 19.83/3.06  fof(f20,axiom,(
% 19.83/3.06    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f38,plain,(
% 19.83/3.06    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 19.83/3.06    inference(ennf_transformation,[],[f20])).
% 19.83/3.06  
% 19.83/3.06  fof(f76,plain,(
% 19.83/3.06    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f38])).
% 19.83/3.06  
% 19.83/3.06  fof(f21,axiom,(
% 19.83/3.06    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 19.83/3.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.06  
% 19.83/3.06  fof(f39,plain,(
% 19.83/3.06    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 19.83/3.06    inference(ennf_transformation,[],[f21])).
% 19.83/3.06  
% 19.83/3.06  fof(f77,plain,(
% 19.83/3.06    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 19.83/3.06    inference(cnf_transformation,[],[f39])).
% 19.83/3.06  
% 19.83/3.06  fof(f89,plain,(
% 19.83/3.06    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 19.83/3.06    inference(cnf_transformation,[],[f53])).
% 19.83/3.06  
% 19.83/3.06  cnf(c_3,plain,
% 19.83/3.06      ( r1_tarski(X0,X0) ),
% 19.83/3.06      inference(cnf_transformation,[],[f105]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1055,plain,
% 19.83/3.06      ( r1_tarski(X0,X0) = iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_9,plain,
% 19.83/3.06      ( ~ r1_tarski(X0,X1)
% 19.83/3.06      | k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1 ),
% 19.83/3.06      inference(cnf_transformation,[],[f102]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1050,plain,
% 19.83/3.06      ( k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) = X1
% 19.83/3.06      | r1_tarski(X0,X1) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_5048,plain,
% 19.83/3.06      ( k2_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = X0 ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1055,c_1050]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_0,plain,
% 19.83/3.06      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 19.83/3.06      inference(cnf_transformation,[],[f97]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_4,plain,
% 19.83/3.06      ( ~ r1_tarski(X0,X1)
% 19.83/3.06      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 19.83/3.06      inference(cnf_transformation,[],[f98]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1054,plain,
% 19.83/3.06      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
% 19.83/3.06      | r1_tarski(X0,X1) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_4396,plain,
% 19.83/3.06      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1055,c_1054]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_4410,plain,
% 19.83/3.06      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.83/3.06      inference(light_normalisation,[status(thm)],[c_4396,c_0]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_5068,plain,
% 19.83/3.06      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.83/3.06      inference(light_normalisation,[status(thm)],[c_5048,c_0,c_4410]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_12,plain,
% 19.83/3.06      ( v1_relat_1(k6_relat_1(X0)) ),
% 19.83/3.06      inference(cnf_transformation,[],[f74]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1047,plain,
% 19.83/3.06      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_17,plain,
% 19.83/3.06      ( ~ v1_relat_1(X0)
% 19.83/3.06      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 19.83/3.06      inference(cnf_transformation,[],[f79]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1042,plain,
% 19.83/3.06      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 19.83/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1957,plain,
% 19.83/3.06      ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1047,c_1042]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_20,plain,
% 19.83/3.06      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 19.83/3.06      inference(cnf_transformation,[],[f83]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_21,plain,
% 19.83/3.06      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 19.83/3.06      inference(cnf_transformation,[],[f82]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1960,plain,
% 19.83/3.06      ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
% 19.83/3.06      inference(light_normalisation,[status(thm)],[c_1957,c_20,c_21]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_26,negated_conjecture,
% 19.83/3.06      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 19.83/3.06      inference(cnf_transformation,[],[f88]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1035,plain,
% 19.83/3.06      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_11,plain,
% 19.83/3.06      ( ~ r1_tarski(X0,X1)
% 19.83/3.06      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
% 19.83/3.06      inference(cnf_transformation,[],[f66]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1048,plain,
% 19.83/3.06      ( r1_tarski(X0,X1) != iProver_top
% 19.83/3.06      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) = iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_6,plain,
% 19.83/3.06      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 19.83/3.06      inference(cnf_transformation,[],[f61]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1052,plain,
% 19.83/3.06      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_3464,plain,
% 19.83/3.06      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1)
% 19.83/3.06      | r1_tarski(X0,X2) != iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1048,c_1052]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_22581,plain,
% 19.83/3.06      ( k2_xboole_0(k2_xboole_0(sK0,X0),k2_xboole_0(k1_relat_1(sK1),X0)) = k2_xboole_0(k1_relat_1(sK1),X0) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1035,c_3464]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_18,plain,
% 19.83/3.06      ( ~ v1_relat_1(X0)
% 19.83/3.06      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 19.83/3.06      inference(cnf_transformation,[],[f80]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1041,plain,
% 19.83/3.06      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 19.83/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_3578,plain,
% 19.83/3.06      ( k2_xboole_0(k10_relat_1(k6_relat_1(X0),X1),k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2)) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1047,c_1041]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_10,plain,
% 19.83/3.06      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 19.83/3.06      inference(cnf_transformation,[],[f65]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1049,plain,
% 19.83/3.06      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_30036,plain,
% 19.83/3.06      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k10_relat_1(k6_relat_1(X0),k2_xboole_0(X1,X2))) = iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_3578,c_1049]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_32461,plain,
% 19.83/3.06      ( r1_tarski(k10_relat_1(k6_relat_1(X0),k2_xboole_0(sK0,X1)),k10_relat_1(k6_relat_1(X0),k2_xboole_0(k1_relat_1(sK1),X1))) = iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_22581,c_30036]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_32958,plain,
% 19.83/3.06      ( r1_tarski(k2_xboole_0(sK0,X0),k10_relat_1(k6_relat_1(k2_xboole_0(sK0,X0)),k2_xboole_0(k1_relat_1(sK1),X0))) = iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1960,c_32461]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_33525,plain,
% 19.83/3.06      ( r1_tarski(k2_xboole_0(sK0,k1_xboole_0),k10_relat_1(k6_relat_1(k2_xboole_0(sK0,k1_xboole_0)),k1_relat_1(sK1))) = iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_5068,c_32958]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_27,negated_conjecture,
% 19.83/3.06      ( v1_relat_1(sK1) ),
% 19.83/3.06      inference(cnf_transformation,[],[f87]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1034,plain,
% 19.83/3.06      ( v1_relat_1(sK1) = iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_19,plain,
% 19.83/3.06      ( ~ v1_relat_1(X0)
% 19.83/3.06      | ~ v1_relat_1(X1)
% 19.83/3.06      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 19.83/3.06      inference(cnf_transformation,[],[f81]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1040,plain,
% 19.83/3.06      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 19.83/3.06      | v1_relat_1(X0) != iProver_top
% 19.83/3.06      | v1_relat_1(X1) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_3138,plain,
% 19.83/3.06      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 19.83/3.06      | v1_relat_1(X1) != iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1047,c_1040]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_17567,plain,
% 19.83/3.06      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1034,c_3138]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_23,plain,
% 19.83/3.06      ( ~ v1_relat_1(X0)
% 19.83/3.06      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 19.83/3.06      inference(cnf_transformation,[],[f85]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1038,plain,
% 19.83/3.06      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 19.83/3.06      | v1_relat_1(X1) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_2096,plain,
% 19.83/3.06      ( k5_relat_1(k6_relat_1(X0),sK1) = k7_relat_1(sK1,X0) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1034,c_1038]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_17568,plain,
% 19.83/3.06      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 19.83/3.06      inference(light_normalisation,[status(thm)],[c_17567,c_2096]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_33605,plain,
% 19.83/3.06      ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,k2_xboole_0(sK0,k1_xboole_0)))) = iProver_top ),
% 19.83/3.06      inference(demodulation,[status(thm)],[c_33525,c_5068,c_17568]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_33606,plain,
% 19.83/3.06      ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top ),
% 19.83/3.06      inference(demodulation,[status(thm)],[c_33605,c_5068]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_34454,plain,
% 19.83/3.06      ( k2_xboole_0(sK0,k5_xboole_0(k1_relat_1(k7_relat_1(sK1,sK0)),k1_setfam_1(k6_enumset1(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k7_relat_1(sK1,sK0)),sK0)))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_33606,c_1050]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_22,plain,
% 19.83/3.06      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 19.83/3.06      inference(cnf_transformation,[],[f84]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1039,plain,
% 19.83/3.06      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 19.83/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_2488,plain,
% 19.83/3.06      ( k2_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1) = X1
% 19.83/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1039,c_1052]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_11605,plain,
% 19.83/3.06      ( k2_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) = X0 ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1034,c_2488]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_11617,plain,
% 19.83/3.06      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0) = iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_11605,c_1049]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_11771,plain,
% 19.83/3.06      ( k5_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),k1_setfam_1(k6_enumset1(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),X0))) = k1_xboole_0 ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_11617,c_1054]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_34464,plain,
% 19.83/3.06      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 19.83/3.06      inference(demodulation,[status(thm)],[c_34454,c_5068,c_11771]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_13,plain,
% 19.83/3.06      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 19.83/3.06      inference(cnf_transformation,[],[f75]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1046,plain,
% 19.83/3.06      ( v1_relat_1(X0) != iProver_top
% 19.83/3.06      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1958,plain,
% 19.83/3.06      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 19.83/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1046,c_1042]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_8551,plain,
% 19.83/3.06      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1034,c_1958]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_24,plain,
% 19.83/3.06      ( ~ v1_relat_1(X0)
% 19.83/3.06      | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 19.83/3.06      inference(cnf_transformation,[],[f103]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1037,plain,
% 19.83/3.06      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 19.83/3.06      | v1_relat_1(X1) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1462,plain,
% 19.83/3.06      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1034,c_1037]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_5,plain,
% 19.83/3.06      ( r1_tarski(X0,X1)
% 19.83/3.06      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0 ),
% 19.83/3.06      inference(cnf_transformation,[],[f99]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1053,plain,
% 19.83/3.06      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != k1_xboole_0
% 19.83/3.06      | r1_tarski(X0,X1) = iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_4349,plain,
% 19.83/3.06      ( k5_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X0),X1)) != k1_xboole_0
% 19.83/3.06      | r1_tarski(X0,k10_relat_1(sK1,X1)) = iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1462,c_1053]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_8901,plain,
% 19.83/3.06      ( k5_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) != k1_xboole_0
% 19.83/3.06      | r1_tarski(X0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X0)))) = iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_8551,c_4349]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_71706,plain,
% 19.83/3.06      ( k5_xboole_0(sK0,sK0) != k1_xboole_0
% 19.83/3.06      | r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))) = iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_34464,c_8901]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_14,plain,
% 19.83/3.06      ( ~ v1_relat_1(X0)
% 19.83/3.06      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 19.83/3.06      inference(cnf_transformation,[],[f76]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1045,plain,
% 19.83/3.06      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 19.83/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_2338,plain,
% 19.83/3.06      ( k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k2_relat_1(k7_relat_1(X0,X1))
% 19.83/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1046,c_1045]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_11293,plain,
% 19.83/3.06      ( k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k7_relat_1(sK1,X0)) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1034,c_2338]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_34617,plain,
% 19.83/3.06      ( k9_relat_1(k7_relat_1(sK1,sK0),sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_34464,c_11293]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_15,plain,
% 19.83/3.06      ( ~ r1_tarski(X0,X1)
% 19.83/3.06      | ~ v1_relat_1(X2)
% 19.83/3.06      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 19.83/3.06      inference(cnf_transformation,[],[f77]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_1044,plain,
% 19.83/3.06      ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
% 19.83/3.06      | r1_tarski(X2,X1) != iProver_top
% 19.83/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.83/3.06      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_4220,plain,
% 19.83/3.06      ( k9_relat_1(k7_relat_1(X0,X1),X1) = k9_relat_1(X0,X1)
% 19.83/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1055,c_1044]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_22247,plain,
% 19.83/3.06      ( k9_relat_1(k7_relat_1(sK1,X0),X0) = k9_relat_1(sK1,X0) ),
% 19.83/3.06      inference(superposition,[status(thm)],[c_1034,c_4220]) ).
% 19.83/3.06  
% 19.83/3.06  cnf(c_34626,plain,
% 19.83/3.06      ( k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(sK1,sK0) ),
% 19.83/3.06      inference(demodulation,[status(thm)],[c_34617,c_22247]) ).
% 19.83/3.07  
% 19.83/3.07  cnf(c_71721,plain,
% 19.83/3.07      ( k5_xboole_0(sK0,sK0) != k1_xboole_0
% 19.83/3.07      | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 19.83/3.07      inference(light_normalisation,[status(thm)],[c_71706,c_34626]) ).
% 19.83/3.07  
% 19.83/3.07  cnf(c_71722,plain,
% 19.83/3.07      ( k1_xboole_0 != k1_xboole_0
% 19.83/3.07      | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 19.83/3.07      inference(demodulation,[status(thm)],[c_71721,c_4410]) ).
% 19.83/3.07  
% 19.83/3.07  cnf(c_71723,plain,
% 19.83/3.07      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 19.83/3.07      inference(equality_resolution_simp,[status(thm)],[c_71722]) ).
% 19.83/3.07  
% 19.83/3.07  cnf(c_25,negated_conjecture,
% 19.83/3.07      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 19.83/3.07      inference(cnf_transformation,[],[f89]) ).
% 19.83/3.07  
% 19.83/3.07  cnf(c_30,plain,
% 19.83/3.07      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 19.83/3.07      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.83/3.07  
% 19.83/3.07  cnf(contradiction,plain,
% 19.83/3.07      ( $false ),
% 19.83/3.07      inference(minisat,[status(thm)],[c_71723,c_30]) ).
% 19.83/3.07  
% 19.83/3.07  
% 19.83/3.07  % SZS output end CNFRefutation for theBenchmark.p
% 19.83/3.07  
% 19.83/3.07  ------                               Statistics
% 19.83/3.07  
% 19.83/3.07  ------ General
% 19.83/3.07  
% 19.83/3.07  abstr_ref_over_cycles:                  0
% 19.83/3.07  abstr_ref_under_cycles:                 0
% 19.83/3.07  gc_basic_clause_elim:                   0
% 19.83/3.07  forced_gc_time:                         0
% 19.83/3.07  parsing_time:                           0.012
% 19.83/3.07  unif_index_cands_time:                  0.
% 19.83/3.07  unif_index_add_time:                    0.
% 19.83/3.07  orderings_time:                         0.
% 19.83/3.07  out_proof_time:                         0.016
% 19.83/3.07  total_time:                             2.352
% 19.83/3.07  num_of_symbols:                         47
% 19.83/3.07  num_of_terms:                           77275
% 19.83/3.07  
% 19.83/3.07  ------ Preprocessing
% 19.83/3.07  
% 19.83/3.07  num_of_splits:                          0
% 19.83/3.07  num_of_split_atoms:                     0
% 19.83/3.07  num_of_reused_defs:                     0
% 19.83/3.07  num_eq_ax_congr_red:                    36
% 19.83/3.07  num_of_sem_filtered_clauses:            1
% 19.83/3.07  num_of_subtypes:                        0
% 19.83/3.07  monotx_restored_types:                  0
% 19.83/3.07  sat_num_of_epr_types:                   0
% 19.83/3.07  sat_num_of_non_cyclic_types:            0
% 19.83/3.07  sat_guarded_non_collapsed_types:        0
% 19.83/3.07  num_pure_diseq_elim:                    0
% 19.83/3.07  simp_replaced_by:                       0
% 19.83/3.07  res_preprocessed:                       135
% 19.83/3.07  prep_upred:                             0
% 19.83/3.07  prep_unflattend:                        0
% 19.83/3.07  smt_new_axioms:                         0
% 19.83/3.07  pred_elim_cands:                        2
% 19.83/3.07  pred_elim:                              0
% 19.83/3.07  pred_elim_cl:                           0
% 19.83/3.07  pred_elim_cycles:                       2
% 19.83/3.07  merged_defs:                            8
% 19.83/3.07  merged_defs_ncl:                        0
% 19.83/3.07  bin_hyper_res:                          8
% 19.83/3.07  prep_cycles:                            4
% 19.83/3.07  pred_elim_time:                         0.001
% 19.83/3.07  splitting_time:                         0.
% 19.83/3.07  sem_filter_time:                        0.
% 19.83/3.07  monotx_time:                            0.001
% 19.83/3.07  subtype_inf_time:                       0.
% 19.83/3.07  
% 19.83/3.07  ------ Problem properties
% 19.83/3.07  
% 19.83/3.07  clauses:                                27
% 19.83/3.07  conjectures:                            3
% 19.83/3.07  epr:                                    3
% 19.83/3.07  horn:                                   27
% 19.83/3.07  ground:                                 3
% 19.83/3.07  unary:                                  10
% 19.83/3.07  binary:                                 14
% 19.83/3.07  lits:                                   47
% 19.83/3.07  lits_eq:                                16
% 19.83/3.07  fd_pure:                                0
% 19.83/3.07  fd_pseudo:                              0
% 19.83/3.07  fd_cond:                                0
% 19.83/3.07  fd_pseudo_cond:                         1
% 19.83/3.07  ac_symbols:                             0
% 19.83/3.07  
% 19.83/3.07  ------ Propositional Solver
% 19.83/3.07  
% 19.83/3.07  prop_solver_calls:                      36
% 19.83/3.07  prop_fast_solver_calls:                 1106
% 19.83/3.07  smt_solver_calls:                       0
% 19.83/3.07  smt_fast_solver_calls:                  0
% 19.83/3.07  prop_num_of_clauses:                    29402
% 19.83/3.07  prop_preprocess_simplified:             47245
% 19.83/3.07  prop_fo_subsumed:                       9
% 19.83/3.07  prop_solver_time:                       0.
% 19.83/3.07  smt_solver_time:                        0.
% 19.83/3.07  smt_fast_solver_time:                   0.
% 19.83/3.07  prop_fast_solver_time:                  0.
% 19.83/3.07  prop_unsat_core_time:                   0.004
% 19.83/3.07  
% 19.83/3.07  ------ QBF
% 19.83/3.07  
% 19.83/3.07  qbf_q_res:                              0
% 19.83/3.07  qbf_num_tautologies:                    0
% 19.83/3.07  qbf_prep_cycles:                        0
% 19.83/3.07  
% 19.83/3.07  ------ BMC1
% 19.83/3.07  
% 19.83/3.07  bmc1_current_bound:                     -1
% 19.83/3.07  bmc1_last_solved_bound:                 -1
% 19.83/3.07  bmc1_unsat_core_size:                   -1
% 19.83/3.07  bmc1_unsat_core_parents_size:           -1
% 19.83/3.07  bmc1_merge_next_fun:                    0
% 19.83/3.07  bmc1_unsat_core_clauses_time:           0.
% 19.83/3.07  
% 19.83/3.07  ------ Instantiation
% 19.83/3.07  
% 19.83/3.07  inst_num_of_clauses:                    7656
% 19.83/3.07  inst_num_in_passive:                    5731
% 19.83/3.07  inst_num_in_active:                     1913
% 19.83/3.07  inst_num_in_unprocessed:                12
% 19.83/3.07  inst_num_of_loops:                      2210
% 19.83/3.07  inst_num_of_learning_restarts:          0
% 19.83/3.07  inst_num_moves_active_passive:          294
% 19.83/3.07  inst_lit_activity:                      0
% 19.83/3.07  inst_lit_activity_moves:                1
% 19.83/3.07  inst_num_tautologies:                   0
% 19.83/3.07  inst_num_prop_implied:                  0
% 19.83/3.07  inst_num_existing_simplified:           0
% 19.83/3.07  inst_num_eq_res_simplified:             0
% 19.83/3.07  inst_num_child_elim:                    0
% 19.83/3.07  inst_num_of_dismatching_blockings:      4136
% 19.83/3.07  inst_num_of_non_proper_insts:           7200
% 19.83/3.07  inst_num_of_duplicates:                 0
% 19.83/3.07  inst_inst_num_from_inst_to_res:         0
% 19.83/3.07  inst_dismatching_checking_time:         0.
% 19.83/3.07  
% 19.83/3.07  ------ Resolution
% 19.83/3.07  
% 19.83/3.07  res_num_of_clauses:                     0
% 19.83/3.07  res_num_in_passive:                     0
% 19.83/3.07  res_num_in_active:                      0
% 19.83/3.07  res_num_of_loops:                       139
% 19.83/3.07  res_forward_subset_subsumed:            1259
% 19.83/3.07  res_backward_subset_subsumed:           0
% 19.83/3.07  res_forward_subsumed:                   0
% 19.83/3.07  res_backward_subsumed:                  0
% 19.83/3.07  res_forward_subsumption_resolution:     0
% 19.83/3.07  res_backward_subsumption_resolution:    0
% 19.83/3.07  res_clause_to_clause_subsumption:       17270
% 19.83/3.07  res_orphan_elimination:                 0
% 19.83/3.07  res_tautology_del:                      498
% 19.83/3.07  res_num_eq_res_simplified:              0
% 19.83/3.07  res_num_sel_changes:                    0
% 19.83/3.07  res_moves_from_active_to_pass:          0
% 19.83/3.07  
% 19.83/3.07  ------ Superposition
% 19.83/3.07  
% 19.83/3.07  sup_time_total:                         0.
% 19.83/3.07  sup_time_generating:                    0.
% 19.83/3.07  sup_time_sim_full:                      0.
% 19.83/3.07  sup_time_sim_immed:                     0.
% 19.83/3.07  
% 19.83/3.07  sup_num_of_clauses:                     3588
% 19.83/3.07  sup_num_in_active:                      379
% 19.83/3.07  sup_num_in_passive:                     3209
% 19.83/3.07  sup_num_of_loops:                       440
% 19.83/3.07  sup_fw_superposition:                   6457
% 19.83/3.07  sup_bw_superposition:                   5085
% 19.83/3.07  sup_immediate_simplified:               5406
% 19.83/3.07  sup_given_eliminated:                   10
% 19.83/3.07  comparisons_done:                       0
% 19.83/3.07  comparisons_avoided:                    0
% 19.83/3.07  
% 19.83/3.07  ------ Simplifications
% 19.83/3.07  
% 19.83/3.07  
% 19.83/3.07  sim_fw_subset_subsumed:                 169
% 19.83/3.07  sim_bw_subset_subsumed:                 37
% 19.83/3.07  sim_fw_subsumed:                        1444
% 19.83/3.07  sim_bw_subsumed:                        81
% 19.83/3.07  sim_fw_subsumption_res:                 0
% 19.83/3.07  sim_bw_subsumption_res:                 0
% 19.83/3.07  sim_tautology_del:                      36
% 19.83/3.07  sim_eq_tautology_del:                   708
% 19.83/3.07  sim_eq_res_simp:                        15
% 19.83/3.07  sim_fw_demodulated:                     2348
% 19.83/3.07  sim_bw_demodulated:                     138
% 19.83/3.07  sim_light_normalised:                   1987
% 19.83/3.07  sim_joinable_taut:                      0
% 19.83/3.07  sim_joinable_simp:                      0
% 19.83/3.07  sim_ac_normalised:                      0
% 19.83/3.07  sim_smt_subsumption:                    0
% 19.83/3.07  
%------------------------------------------------------------------------------
