%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:09 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 227 expanded)
%              Number of clauses        :   48 (  55 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  170 ( 302 expanded)
%              Number of equality atoms :  114 ( 240 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f28,f45,f46])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f33,f47,f48])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k1_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) ),
    inference(definition_unfolding,[],[f29,f45,f48])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k1_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X3,X2,X1),k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f27,f47,f47])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f44,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f38,f31])).

fof(f56,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_0,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_106,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0_39,X0_39,X1_39),k1_enumset1(X0_39,X0_39,X1_39),k1_enumset1(X2_39,X2_39,X2_39))) = k1_enumset1(X0_39,X1_39,X2_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_103,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X3_39,X3_39,X3_39))) = k5_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_298,plain,
    ( k5_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k1_enumset1(X0_39,X1_39,X2_39) ),
    inference(superposition,[status(thm)],[c_106,c_103])).

cnf(c_1,plain,
    ( k3_tarski(k1_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_105,plain,
    ( k3_tarski(k1_enumset1(k5_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k5_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k1_enumset1(X4_39,X5_39,X6_39))) = k5_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_419,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X3_39,X4_39,X5_39))) = k5_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39) ),
    inference(superposition,[status(thm)],[c_298,c_105])).

cnf(c_1030,plain,
    ( k5_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X2_39,X2_39) = k1_enumset1(X0_39,X1_39,X2_39) ),
    inference(superposition,[status(thm)],[c_419,c_106])).

cnf(c_2,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X3,X2,X1),k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_104,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X3_39,X3_39,X3_39))) = k3_tarski(k1_enumset1(k1_enumset1(X3_39,X2_39,X1_39),k1_enumset1(X3_39,X2_39,X1_39),k1_enumset1(X0_39,X0_39,X0_39))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_308,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X2_39,X2_39,X2_39))) = k1_enumset1(X2_39,X1_39,X0_39) ),
    inference(superposition,[status(thm)],[c_104,c_106])).

cnf(c_628,plain,
    ( k5_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X2_39) = k1_enumset1(X2_39,X1_39,X0_39) ),
    inference(superposition,[status(thm)],[c_308,c_103])).

cnf(c_1134,plain,
    ( k1_enumset1(X0_39,X0_39,X1_39) = k1_enumset1(X1_39,X1_39,X0_39) ),
    inference(superposition,[status(thm)],[c_1030,c_628])).

cnf(c_8,negated_conjecture,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_98,negated_conjecture,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_7764,plain,
    ( k7_relat_1(sK1,k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))) != k7_relat_1(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_1134,c_98])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_101,plain,
    ( ~ v1_relat_1(X0_38)
    | k7_relat_1(X0_38,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3710,plain,
    ( ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_110,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_456,plain,
    ( X0_38 != X1_38
    | X0_38 = k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) != X1_38 ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_665,plain,
    ( X0_38 != k7_relat_1(X1_38,X0_39)
    | X0_38 = k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) != k7_relat_1(X1_38,X0_39) ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_717,plain,
    ( k7_relat_1(X0_38,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) != k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39)
    | k7_relat_1(X0_38,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_2355,plain,
    ( k7_relat_1(sK1,k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | k7_relat_1(sK1,k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))) = k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_332,plain,
    ( X0_38 != X1_38
    | k7_relat_1(sK1,sK0) != X1_38
    | k7_relat_1(sK1,sK0) = X0_38 ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_384,plain,
    ( X0_38 != k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) = X0_38
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_458,plain,
    ( k7_relat_1(X0_38,X0_39) != k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) = k7_relat_1(X0_38,X0_39)
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_852,plain,
    ( k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39) != k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39)
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_1417,plain,
    ( k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) != k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_7,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_99,plain,
    ( ~ r1_tarski(k1_relat_1(X0_38),X0_39)
    | ~ v1_relat_1(X0_38)
    | k7_relat_1(X0_38,X0_39) = X0_38 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_285,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0_38,X0_39)),k1_relat_1(X0_38))
    | ~ v1_relat_1(k7_relat_1(X0_38,X0_39))
    | k7_relat_1(k7_relat_1(X0_38,X0_39),k1_relat_1(X0_38)) = k7_relat_1(X0_38,X0_39) ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_287,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) = k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_6,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_100,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_38,X0_39)),k1_relat_1(X0_38))
    | ~ v1_relat_1(X0_38) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_140,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_102,plain,
    ( ~ v1_relat_1(X0_38)
    | v1_relat_1(k7_relat_1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_134,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_109,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_128,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_108,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_127,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_114,plain,
    ( X0_39 != X1_39
    | X0_38 != X1_38
    | k7_relat_1(X0_38,X0_39) = k7_relat_1(X1_38,X1_39) ),
    theory(equality)).

cnf(c_121,plain,
    ( sK0 != sK0
    | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,sK0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7764,c_3710,c_2355,c_1417,c_287,c_140,c_134,c_128,c_127,c_121,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:36:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.83/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/0.95  
% 3.83/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.95  
% 3.83/0.95  ------  iProver source info
% 3.83/0.95  
% 3.83/0.95  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.95  git: non_committed_changes: false
% 3.83/0.95  git: last_make_outside_of_git: false
% 3.83/0.95  
% 3.83/0.95  ------ 
% 3.83/0.95  ------ Parsing...
% 3.83/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.95  
% 3.83/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.83/0.95  
% 3.83/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.95  
% 3.83/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.95  ------ Proving...
% 3.83/0.95  ------ Problem Properties 
% 3.83/0.95  
% 3.83/0.95  
% 3.83/0.95  clauses                                 10
% 3.83/0.95  conjectures                             2
% 3.83/0.95  EPR                                     1
% 3.83/0.95  Horn                                    10
% 3.83/0.95  unary                                   6
% 3.83/0.95  binary                                  3
% 3.83/0.95  lits                                    15
% 3.83/0.95  lits eq                                 7
% 3.83/0.95  fd_pure                                 0
% 3.83/0.95  fd_pseudo                               0
% 3.83/0.95  fd_cond                                 0
% 3.83/0.95  fd_pseudo_cond                          0
% 3.83/0.95  AC symbols                              0
% 3.83/0.95  
% 3.83/0.95  ------ Input Options Time Limit: Unbounded
% 3.83/0.95  
% 3.83/0.95  
% 3.83/0.95  ------ 
% 3.83/0.95  Current options:
% 3.83/0.95  ------ 
% 3.83/0.95  
% 3.83/0.95  
% 3.83/0.95  
% 3.83/0.95  
% 3.83/0.95  ------ Proving...
% 3.83/0.95  
% 3.83/0.95  
% 3.83/0.95  % SZS status Theorem for theBenchmark.p
% 3.83/0.95  
% 3.83/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.95  
% 3.83/0.95  fof(f6,axiom,(
% 3.83/0.95    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f32,plain,(
% 3.83/0.95    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f6])).
% 3.83/0.95  
% 3.83/0.95  fof(f2,axiom,(
% 3.83/0.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f28,plain,(
% 3.83/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 3.83/0.95    inference(cnf_transformation,[],[f2])).
% 3.83/0.95  
% 3.83/0.95  fof(f11,axiom,(
% 3.83/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f37,plain,(
% 3.83/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.83/0.95    inference(cnf_transformation,[],[f11])).
% 3.83/0.95  
% 3.83/0.95  fof(f45,plain,(
% 3.83/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.83/0.95    inference(definition_unfolding,[],[f37,f31])).
% 3.83/0.95  
% 3.83/0.95  fof(f4,axiom,(
% 3.83/0.95    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f30,plain,(
% 3.83/0.95    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f4])).
% 3.83/0.95  
% 3.83/0.95  fof(f5,axiom,(
% 3.83/0.95    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f31,plain,(
% 3.83/0.95    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f5])).
% 3.83/0.95  
% 3.83/0.95  fof(f46,plain,(
% 3.83/0.95    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 3.83/0.95    inference(definition_unfolding,[],[f30,f31])).
% 3.83/0.95  
% 3.83/0.95  fof(f47,plain,(
% 3.83/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 3.83/0.95    inference(definition_unfolding,[],[f28,f45,f46])).
% 3.83/0.95  
% 3.83/0.95  fof(f51,plain,(
% 3.83/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 3.83/0.95    inference(definition_unfolding,[],[f32,f47])).
% 3.83/0.95  
% 3.83/0.95  fof(f7,axiom,(
% 3.83/0.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f33,plain,(
% 3.83/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f7])).
% 3.83/0.95  
% 3.83/0.95  fof(f8,axiom,(
% 3.83/0.95    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f34,plain,(
% 3.83/0.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f8])).
% 3.83/0.95  
% 3.83/0.95  fof(f9,axiom,(
% 3.83/0.95    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f35,plain,(
% 3.83/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f9])).
% 3.83/0.95  
% 3.83/0.95  fof(f48,plain,(
% 3.83/0.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.83/0.95    inference(definition_unfolding,[],[f34,f35])).
% 3.83/0.95  
% 3.83/0.95  fof(f54,plain,(
% 3.83/0.95    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 3.83/0.95    inference(definition_unfolding,[],[f33,f47,f48])).
% 3.83/0.95  
% 3.83/0.95  fof(f10,axiom,(
% 3.83/0.95    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f36,plain,(
% 3.83/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f10])).
% 3.83/0.95  
% 3.83/0.95  fof(f3,axiom,(
% 3.83/0.95    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f29,plain,(
% 3.83/0.95    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f3])).
% 3.83/0.95  
% 3.83/0.95  fof(f49,plain,(
% 3.83/0.95    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k1_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)))) )),
% 3.83/0.95    inference(definition_unfolding,[],[f29,f45,f48])).
% 3.83/0.95  
% 3.83/0.95  fof(f52,plain,(
% 3.83/0.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k1_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k1_enumset1(X4,X5,X6)))) )),
% 3.83/0.95    inference(definition_unfolding,[],[f36,f49])).
% 3.83/0.95  
% 3.83/0.95  fof(f1,axiom,(
% 3.83/0.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f27,plain,(
% 3.83/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f1])).
% 3.83/0.95  
% 3.83/0.95  fof(f53,plain,(
% 3.83/0.95    ( ! [X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X3,X2,X1),k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0)))) )),
% 3.83/0.95    inference(definition_unfolding,[],[f27,f47,f47])).
% 3.83/0.95  
% 3.83/0.95  fof(f17,conjecture,(
% 3.83/0.95    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f18,negated_conjecture,(
% 3.83/0.95    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 3.83/0.95    inference(negated_conjecture,[],[f17])).
% 3.83/0.95  
% 3.83/0.95  fof(f24,plain,(
% 3.83/0.95    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 3.83/0.95    inference(ennf_transformation,[],[f18])).
% 3.83/0.95  
% 3.83/0.95  fof(f25,plain,(
% 3.83/0.95    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 3.83/0.95    introduced(choice_axiom,[])).
% 3.83/0.95  
% 3.83/0.95  fof(f26,plain,(
% 3.83/0.95    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 3.83/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 3.83/0.95  
% 3.83/0.95  fof(f44,plain,(
% 3.83/0.95    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 3.83/0.95    inference(cnf_transformation,[],[f26])).
% 3.83/0.95  
% 3.83/0.95  fof(f12,axiom,(
% 3.83/0.95    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f38,plain,(
% 3.83/0.95    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f12])).
% 3.83/0.95  
% 3.83/0.95  fof(f50,plain,(
% 3.83/0.95    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.83/0.95    inference(definition_unfolding,[],[f38,f31])).
% 3.83/0.95  
% 3.83/0.95  fof(f56,plain,(
% 3.83/0.95    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0)))),
% 3.83/0.95    inference(definition_unfolding,[],[f44,f50])).
% 3.83/0.95  
% 3.83/0.95  fof(f14,axiom,(
% 3.83/0.95    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f20,plain,(
% 3.83/0.95    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.83/0.95    inference(ennf_transformation,[],[f14])).
% 3.83/0.95  
% 3.83/0.95  fof(f40,plain,(
% 3.83/0.95    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f20])).
% 3.83/0.95  
% 3.83/0.95  fof(f55,plain,(
% 3.83/0.95    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 3.83/0.95    inference(definition_unfolding,[],[f40,f50])).
% 3.83/0.95  
% 3.83/0.95  fof(f16,axiom,(
% 3.83/0.95    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f22,plain,(
% 3.83/0.95    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.83/0.95    inference(ennf_transformation,[],[f16])).
% 3.83/0.95  
% 3.83/0.95  fof(f23,plain,(
% 3.83/0.95    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.83/0.95    inference(flattening,[],[f22])).
% 3.83/0.95  
% 3.83/0.95  fof(f42,plain,(
% 3.83/0.95    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f23])).
% 3.83/0.95  
% 3.83/0.95  fof(f15,axiom,(
% 3.83/0.95    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f21,plain,(
% 3.83/0.95    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.83/0.95    inference(ennf_transformation,[],[f15])).
% 3.83/0.95  
% 3.83/0.95  fof(f41,plain,(
% 3.83/0.95    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f21])).
% 3.83/0.95  
% 3.83/0.95  fof(f13,axiom,(
% 3.83/0.95    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.83/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.95  
% 3.83/0.95  fof(f19,plain,(
% 3.83/0.95    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.83/0.95    inference(ennf_transformation,[],[f13])).
% 3.83/0.95  
% 3.83/0.95  fof(f39,plain,(
% 3.83/0.95    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.83/0.95    inference(cnf_transformation,[],[f19])).
% 3.83/0.95  
% 3.83/0.95  fof(f43,plain,(
% 3.83/0.95    v1_relat_1(sK1)),
% 3.83/0.95    inference(cnf_transformation,[],[f26])).
% 3.83/0.95  
% 3.83/0.95  cnf(c_0,plain,
% 3.83/0.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
% 3.83/0.95      inference(cnf_transformation,[],[f51]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_106,plain,
% 3.83/0.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0_39,X0_39,X1_39),k1_enumset1(X0_39,X0_39,X1_39),k1_enumset1(X2_39,X2_39,X2_39))) = k1_enumset1(X0_39,X1_39,X2_39) ),
% 3.83/0.95      inference(subtyping,[status(esa)],[c_0]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_3,plain,
% 3.83/0.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
% 3.83/0.95      inference(cnf_transformation,[],[f54]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_103,plain,
% 3.83/0.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X3_39,X3_39,X3_39))) = k5_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39) ),
% 3.83/0.95      inference(subtyping,[status(esa)],[c_3]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_298,plain,
% 3.83/0.95      ( k5_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,X1_39,X2_39) = k1_enumset1(X0_39,X1_39,X2_39) ),
% 3.83/0.95      inference(superposition,[status(thm)],[c_106,c_103]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_1,plain,
% 3.83/0.95      ( k3_tarski(k1_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 3.83/0.95      inference(cnf_transformation,[],[f52]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_105,plain,
% 3.83/0.95      ( k3_tarski(k1_enumset1(k5_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k5_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X3_39),k1_enumset1(X4_39,X5_39,X6_39))) = k5_enumset1(X0_39,X1_39,X2_39,X3_39,X4_39,X5_39,X6_39) ),
% 3.83/0.95      inference(subtyping,[status(esa)],[c_1]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_419,plain,
% 3.83/0.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X3_39,X4_39,X5_39))) = k5_enumset1(X0_39,X0_39,X1_39,X2_39,X3_39,X4_39,X5_39) ),
% 3.83/0.95      inference(superposition,[status(thm)],[c_298,c_105]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_1030,plain,
% 3.83/0.95      ( k5_enumset1(X0_39,X0_39,X0_39,X1_39,X2_39,X2_39,X2_39) = k1_enumset1(X0_39,X1_39,X2_39) ),
% 3.83/0.95      inference(superposition,[status(thm)],[c_419,c_106]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_2,plain,
% 3.83/0.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X3,X2,X1),k1_enumset1(X3,X2,X1),k1_enumset1(X0,X0,X0))) ),
% 3.83/0.95      inference(cnf_transformation,[],[f53]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_104,plain,
% 3.83/0.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X3_39,X3_39,X3_39))) = k3_tarski(k1_enumset1(k1_enumset1(X3_39,X2_39,X1_39),k1_enumset1(X3_39,X2_39,X1_39),k1_enumset1(X0_39,X0_39,X0_39))) ),
% 3.83/0.95      inference(subtyping,[status(esa)],[c_2]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_308,plain,
% 3.83/0.95      ( k3_tarski(k1_enumset1(k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X0_39,X1_39,X2_39),k1_enumset1(X2_39,X2_39,X2_39))) = k1_enumset1(X2_39,X1_39,X0_39) ),
% 3.83/0.95      inference(superposition,[status(thm)],[c_104,c_106]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_628,plain,
% 3.83/0.95      ( k5_enumset1(X0_39,X0_39,X0_39,X0_39,X1_39,X2_39,X2_39) = k1_enumset1(X2_39,X1_39,X0_39) ),
% 3.83/0.95      inference(superposition,[status(thm)],[c_308,c_103]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_1134,plain,
% 3.83/0.95      ( k1_enumset1(X0_39,X0_39,X1_39) = k1_enumset1(X1_39,X1_39,X0_39) ),
% 3.83/0.95      inference(superposition,[status(thm)],[c_1030,c_628]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_8,negated_conjecture,
% 3.83/0.95      ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
% 3.83/0.95      inference(cnf_transformation,[],[f56]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_98,negated_conjecture,
% 3.83/0.95      ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
% 3.83/0.95      inference(subtyping,[status(esa)],[c_8]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_7764,plain,
% 3.83/0.95      ( k7_relat_1(sK1,k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))) != k7_relat_1(sK1,sK0) ),
% 3.83/0.95      inference(superposition,[status(thm)],[c_1134,c_98]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_5,plain,
% 3.83/0.95      ( ~ v1_relat_1(X0)
% 3.83/0.95      | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.83/0.95      inference(cnf_transformation,[],[f55]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_101,plain,
% 3.83/0.95      ( ~ v1_relat_1(X0_38)
% 3.83/0.95      | k7_relat_1(X0_38,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39) ),
% 3.83/0.95      inference(subtyping,[status(esa)],[c_5]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_3710,plain,
% 3.83/0.95      ( ~ v1_relat_1(sK1)
% 3.83/0.95      | k7_relat_1(sK1,k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_101]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_110,plain,
% 3.83/0.95      ( X0_38 != X1_38 | X2_38 != X1_38 | X2_38 = X0_38 ),
% 3.83/0.95      theory(equality) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_456,plain,
% 3.83/0.95      ( X0_38 != X1_38
% 3.83/0.95      | X0_38 = k7_relat_1(sK1,sK0)
% 3.83/0.95      | k7_relat_1(sK1,sK0) != X1_38 ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_110]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_665,plain,
% 3.83/0.95      ( X0_38 != k7_relat_1(X1_38,X0_39)
% 3.83/0.95      | X0_38 = k7_relat_1(sK1,sK0)
% 3.83/0.95      | k7_relat_1(sK1,sK0) != k7_relat_1(X1_38,X0_39) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_456]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_717,plain,
% 3.83/0.95      ( k7_relat_1(X0_38,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) != k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39)
% 3.83/0.95      | k7_relat_1(X0_38,k1_setfam_1(k1_enumset1(X0_39,X0_39,X1_39))) = k7_relat_1(sK1,sK0)
% 3.83/0.95      | k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_665]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_2355,plain,
% 3.83/0.95      ( k7_relat_1(sK1,k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
% 3.83/0.95      | k7_relat_1(sK1,k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))) = k7_relat_1(sK1,sK0)
% 3.83/0.95      | k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_717]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_332,plain,
% 3.83/0.95      ( X0_38 != X1_38
% 3.83/0.95      | k7_relat_1(sK1,sK0) != X1_38
% 3.83/0.95      | k7_relat_1(sK1,sK0) = X0_38 ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_110]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_384,plain,
% 3.83/0.95      ( X0_38 != k7_relat_1(sK1,sK0)
% 3.83/0.95      | k7_relat_1(sK1,sK0) = X0_38
% 3.83/0.95      | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_332]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_458,plain,
% 3.83/0.95      ( k7_relat_1(X0_38,X0_39) != k7_relat_1(sK1,sK0)
% 3.83/0.95      | k7_relat_1(sK1,sK0) = k7_relat_1(X0_38,X0_39)
% 3.83/0.95      | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_384]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_852,plain,
% 3.83/0.95      ( k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39) != k7_relat_1(sK1,sK0)
% 3.83/0.95      | k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(X0_38,X0_39),X1_39)
% 3.83/0.95      | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_458]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_1417,plain,
% 3.83/0.95      ( k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) != k7_relat_1(sK1,sK0)
% 3.83/0.95      | k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
% 3.83/0.95      | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_852]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_7,plain,
% 3.83/0.95      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.83/0.95      | ~ v1_relat_1(X0)
% 3.83/0.95      | k7_relat_1(X0,X1) = X0 ),
% 3.83/0.95      inference(cnf_transformation,[],[f42]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_99,plain,
% 3.83/0.95      ( ~ r1_tarski(k1_relat_1(X0_38),X0_39)
% 3.83/0.95      | ~ v1_relat_1(X0_38)
% 3.83/0.95      | k7_relat_1(X0_38,X0_39) = X0_38 ),
% 3.83/0.95      inference(subtyping,[status(esa)],[c_7]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_285,plain,
% 3.83/0.95      ( ~ r1_tarski(k1_relat_1(k7_relat_1(X0_38,X0_39)),k1_relat_1(X0_38))
% 3.83/0.95      | ~ v1_relat_1(k7_relat_1(X0_38,X0_39))
% 3.83/0.95      | k7_relat_1(k7_relat_1(X0_38,X0_39),k1_relat_1(X0_38)) = k7_relat_1(X0_38,X0_39) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_99]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_287,plain,
% 3.83/0.95      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
% 3.83/0.95      | ~ v1_relat_1(k7_relat_1(sK1,sK0))
% 3.83/0.95      | k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) = k7_relat_1(sK1,sK0) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_285]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_6,plain,
% 3.83/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 3.83/0.95      | ~ v1_relat_1(X0) ),
% 3.83/0.95      inference(cnf_transformation,[],[f41]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_100,plain,
% 3.83/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0_38,X0_39)),k1_relat_1(X0_38))
% 3.83/0.95      | ~ v1_relat_1(X0_38) ),
% 3.83/0.95      inference(subtyping,[status(esa)],[c_6]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_140,plain,
% 3.83/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
% 3.83/0.95      | ~ v1_relat_1(sK1) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_100]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_4,plain,
% 3.83/0.95      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.83/0.95      inference(cnf_transformation,[],[f39]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_102,plain,
% 3.83/0.95      ( ~ v1_relat_1(X0_38) | v1_relat_1(k7_relat_1(X0_38,X0_39)) ),
% 3.83/0.95      inference(subtyping,[status(esa)],[c_4]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_134,plain,
% 3.83/0.95      ( v1_relat_1(k7_relat_1(sK1,sK0)) | ~ v1_relat_1(sK1) ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_102]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_109,plain,( X0_39 = X0_39 ),theory(equality) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_128,plain,
% 3.83/0.95      ( sK0 = sK0 ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_109]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_108,plain,( X0_38 = X0_38 ),theory(equality) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_127,plain,
% 3.83/0.95      ( sK1 = sK1 ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_108]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_114,plain,
% 3.83/0.95      ( X0_39 != X1_39
% 3.83/0.95      | X0_38 != X1_38
% 3.83/0.95      | k7_relat_1(X0_38,X0_39) = k7_relat_1(X1_38,X1_39) ),
% 3.83/0.95      theory(equality) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_121,plain,
% 3.83/0.95      ( sK0 != sK0
% 3.83/0.95      | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,sK0)
% 3.83/0.95      | sK1 != sK1 ),
% 3.83/0.95      inference(instantiation,[status(thm)],[c_114]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(c_9,negated_conjecture,
% 3.83/0.95      ( v1_relat_1(sK1) ),
% 3.83/0.95      inference(cnf_transformation,[],[f43]) ).
% 3.83/0.95  
% 3.83/0.95  cnf(contradiction,plain,
% 3.83/0.95      ( $false ),
% 3.83/0.95      inference(minisat,
% 3.83/0.95                [status(thm)],
% 3.83/0.95                [c_7764,c_3710,c_2355,c_1417,c_287,c_140,c_134,c_128,
% 3.83/0.95                 c_127,c_121,c_9]) ).
% 3.83/0.95  
% 3.83/0.95  
% 3.83/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.95  
% 3.83/0.95  ------                               Statistics
% 3.83/0.95  
% 3.83/0.95  ------ Selected
% 3.83/0.95  
% 3.83/0.95  total_time:                             0.259
% 3.83/0.95  
%------------------------------------------------------------------------------
