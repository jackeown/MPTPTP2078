%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:44 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 246 expanded)
%              Number of clauses        :   23 (  29 expanded)
%              Number of leaves         :   16 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :   97 ( 297 expanded)
%              Number of equality atoms :   70 ( 243 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f53])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f29])).

fof(f50,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f31,f57,f57])).

fof(f51,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_134,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_135,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_134])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_360,plain,
    ( k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_135,c_6])).

cnf(c_4,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_314,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_525,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_135,c_314])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_313,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1126,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_525,c_313])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_366,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k6_subset_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_4143,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_1126,c_366])).

cnf(c_11,negated_conjecture,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4790,plain,
    ( k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_4143,c_11])).

cnf(c_4796,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(superposition,[status(thm)],[c_360,c_4790])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1))) = k6_subset_1(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_140,plain,
    ( k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1))) = k6_subset_1(k1_relat_1(X0),X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_141,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_140])).

cnf(c_482,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4796,c_482])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.45/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/0.98  
% 3.45/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.98  
% 3.45/0.98  ------  iProver source info
% 3.45/0.98  
% 3.45/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.98  git: non_committed_changes: false
% 3.45/0.98  git: last_make_outside_of_git: false
% 3.45/0.98  
% 3.45/0.98  ------ 
% 3.45/0.98  ------ Parsing...
% 3.45/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.98  
% 3.45/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.98  ------ Proving...
% 3.45/0.98  ------ Problem Properties 
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  clauses                                 11
% 3.45/0.98  conjectures                             1
% 3.45/0.98  EPR                                     2
% 3.45/0.98  Horn                                    11
% 3.45/0.98  unary                                   8
% 3.45/0.98  binary                                  2
% 3.45/0.98  lits                                    15
% 3.45/0.98  lits eq                                 9
% 3.45/0.98  fd_pure                                 0
% 3.45/0.98  fd_pseudo                               0
% 3.45/0.98  fd_cond                                 0
% 3.45/0.98  fd_pseudo_cond                          1
% 3.45/0.98  AC symbols                              0
% 3.45/0.98  
% 3.45/0.98  ------ Input Options Time Limit: Unbounded
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  ------ 
% 3.45/0.98  Current options:
% 3.45/0.98  ------ 
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  ------ Proving...
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  % SZS status Theorem for theBenchmark.p
% 3.45/0.98  
% 3.45/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.98  
% 3.45/0.98  fof(f16,axiom,(
% 3.45/0.98    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f23,plain,(
% 3.45/0.98    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.45/0.98    inference(ennf_transformation,[],[f16])).
% 3.45/0.98  
% 3.45/0.98  fof(f48,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f23])).
% 3.45/0.98  
% 3.45/0.98  fof(f13,axiom,(
% 3.45/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f45,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.45/0.98    inference(cnf_transformation,[],[f13])).
% 3.45/0.98  
% 3.45/0.98  fof(f6,axiom,(
% 3.45/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f38,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f6])).
% 3.45/0.98  
% 3.45/0.98  fof(f7,axiom,(
% 3.45/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f39,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f7])).
% 3.45/0.98  
% 3.45/0.98  fof(f8,axiom,(
% 3.45/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f40,plain,(
% 3.45/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f8])).
% 3.45/0.98  
% 3.45/0.98  fof(f9,axiom,(
% 3.45/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f41,plain,(
% 3.45/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f9])).
% 3.45/0.98  
% 3.45/0.98  fof(f10,axiom,(
% 3.45/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f42,plain,(
% 3.45/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f10])).
% 3.45/0.98  
% 3.45/0.98  fof(f11,axiom,(
% 3.45/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f43,plain,(
% 3.45/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f11])).
% 3.45/0.98  
% 3.45/0.98  fof(f52,plain,(
% 3.45/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.45/0.98    inference(definition_unfolding,[],[f42,f43])).
% 3.45/0.98  
% 3.45/0.98  fof(f53,plain,(
% 3.45/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.45/0.98    inference(definition_unfolding,[],[f41,f52])).
% 3.45/0.98  
% 3.45/0.98  fof(f54,plain,(
% 3.45/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.45/0.98    inference(definition_unfolding,[],[f40,f53])).
% 3.45/0.98  
% 3.45/0.98  fof(f55,plain,(
% 3.45/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.45/0.98    inference(definition_unfolding,[],[f39,f54])).
% 3.45/0.98  
% 3.45/0.98  fof(f56,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.45/0.98    inference(definition_unfolding,[],[f38,f55])).
% 3.45/0.98  
% 3.45/0.98  fof(f57,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.45/0.98    inference(definition_unfolding,[],[f45,f56])).
% 3.45/0.98  
% 3.45/0.98  fof(f63,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.45/0.98    inference(definition_unfolding,[],[f48,f57])).
% 3.45/0.98  
% 3.45/0.98  fof(f18,conjecture,(
% 3.45/0.98    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f19,negated_conjecture,(
% 3.45/0.98    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 3.45/0.98    inference(negated_conjecture,[],[f18])).
% 3.45/0.98  
% 3.45/0.98  fof(f26,plain,(
% 3.45/0.98    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.45/0.98    inference(ennf_transformation,[],[f19])).
% 3.45/0.98  
% 3.45/0.98  fof(f29,plain,(
% 3.45/0.98    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 3.45/0.98    introduced(choice_axiom,[])).
% 3.45/0.98  
% 3.45/0.98  fof(f30,plain,(
% 3.45/0.98    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 3.45/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f29])).
% 3.45/0.98  
% 3.45/0.98  fof(f50,plain,(
% 3.45/0.98    v1_relat_1(sK1)),
% 3.45/0.98    inference(cnf_transformation,[],[f30])).
% 3.45/0.98  
% 3.45/0.98  fof(f12,axiom,(
% 3.45/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f44,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f12])).
% 3.45/0.98  
% 3.45/0.98  fof(f3,axiom,(
% 3.45/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f35,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.45/0.98    inference(cnf_transformation,[],[f3])).
% 3.45/0.98  
% 3.45/0.98  fof(f58,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.45/0.98    inference(definition_unfolding,[],[f35,f57])).
% 3.45/0.98  
% 3.45/0.98  fof(f62,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1)) )),
% 3.45/0.98    inference(definition_unfolding,[],[f44,f58])).
% 3.45/0.98  
% 3.45/0.98  fof(f4,axiom,(
% 3.45/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f36,plain,(
% 3.45/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f4])).
% 3.45/0.98  
% 3.45/0.98  fof(f60,plain,(
% 3.45/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 3.45/0.98    inference(definition_unfolding,[],[f36,f57])).
% 3.45/0.98  
% 3.45/0.98  fof(f5,axiom,(
% 3.45/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f20,plain,(
% 3.45/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.45/0.98    inference(ennf_transformation,[],[f5])).
% 3.45/0.98  
% 3.45/0.98  fof(f37,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f20])).
% 3.45/0.98  
% 3.45/0.98  fof(f61,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.45/0.98    inference(definition_unfolding,[],[f37,f57])).
% 3.45/0.98  
% 3.45/0.98  fof(f1,axiom,(
% 3.45/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f31,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f1])).
% 3.45/0.98  
% 3.45/0.98  fof(f59,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 3.45/0.98    inference(definition_unfolding,[],[f31,f57,f57])).
% 3.45/0.98  
% 3.45/0.98  fof(f51,plain,(
% 3.45/0.98    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 3.45/0.98    inference(cnf_transformation,[],[f30])).
% 3.45/0.98  
% 3.45/0.98  fof(f15,axiom,(
% 3.45/0.98    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 3.45/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.98  
% 3.45/0.98  fof(f22,plain,(
% 3.45/0.98    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.45/0.98    inference(ennf_transformation,[],[f15])).
% 3.45/0.98  
% 3.45/0.98  fof(f47,plain,(
% 3.45/0.98    ( ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 3.45/0.98    inference(cnf_transformation,[],[f22])).
% 3.45/0.98  
% 3.45/0.98  cnf(c_9,plain,
% 3.45/0.98      ( ~ v1_relat_1(X0)
% 3.45/0.98      | k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.45/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_12,negated_conjecture,
% 3.45/0.98      ( v1_relat_1(sK1) ),
% 3.45/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_134,plain,
% 3.45/0.98      ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.45/0.98      | sK1 != X0 ),
% 3.45/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_135,plain,
% 3.45/0.98      ( k1_setfam_1(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.45/0.98      inference(unflattening,[status(thm)],[c_134]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_6,plain,
% 3.45/0.98      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
% 3.45/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_360,plain,
% 3.45/0.98      ( k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_135,c_6]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4,plain,
% 3.45/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
% 3.45/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_314,plain,
% 3.45/0.98      ( r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_525,plain,
% 3.45/0.98      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1)) = iProver_top ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_135,c_314]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_5,plain,
% 3.45/0.98      ( ~ r1_tarski(X0,X1)
% 3.45/0.98      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 3.45/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_313,plain,
% 3.45/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 3.45/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.45/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_1126,plain,
% 3.45/0.98      ( k1_setfam_1(k6_enumset1(k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(k7_relat_1(sK1,X0)),k1_relat_1(sK1))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_525,c_313]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_0,plain,
% 3.45/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
% 3.45/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_366,plain,
% 3.45/0.98      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k6_subset_1(X0,X1) ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4143,plain,
% 3.45/0.98      ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) = k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_1126,c_366]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_11,negated_conjecture,
% 3.45/0.98      ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
% 3.45/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4790,plain,
% 3.45/0.98      ( k5_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_4143,c_11]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_4796,plain,
% 3.45/0.98      ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
% 3.45/0.98      inference(superposition,[status(thm)],[c_360,c_4790]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_8,plain,
% 3.45/0.98      ( ~ v1_relat_1(X0)
% 3.45/0.98      | k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1))) = k6_subset_1(k1_relat_1(X0),X1) ),
% 3.45/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_140,plain,
% 3.45/0.98      ( k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1))) = k6_subset_1(k1_relat_1(X0),X1)
% 3.45/0.98      | sK1 != X0 ),
% 3.45/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_141,plain,
% 3.45/0.98      ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
% 3.45/0.98      inference(unflattening,[status(thm)],[c_140]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(c_482,plain,
% 3.45/0.98      ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),sK0) ),
% 3.45/0.98      inference(instantiation,[status(thm)],[c_141]) ).
% 3.45/0.98  
% 3.45/0.98  cnf(contradiction,plain,
% 3.45/0.98      ( $false ),
% 3.45/0.98      inference(minisat,[status(thm)],[c_4796,c_482]) ).
% 3.45/0.98  
% 3.45/0.98  
% 3.45/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/0.98  
% 3.45/0.98  ------                               Statistics
% 3.45/0.98  
% 3.45/0.98  ------ Selected
% 3.45/0.98  
% 3.45/0.98  total_time:                             0.277
% 3.45/0.98  
%------------------------------------------------------------------------------
