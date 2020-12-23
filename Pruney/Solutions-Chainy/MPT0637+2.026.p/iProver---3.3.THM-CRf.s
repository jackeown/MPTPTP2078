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
% DateTime   : Thu Dec  3 11:50:00 EST 2020

% Result     : Theorem 15.58s
% Output     : CNFRefutation 15.58s
% Verified   : 
% Statistics : Number of formulae       :  152 (8753 expanded)
%              Number of clauses        :   98 (2934 expanded)
%              Number of leaves         :   16 (2195 expanded)
%              Depth                    :   34
%              Number of atoms          :  255 (11551 expanded)
%              Number of equality atoms :  168 (8091 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f58,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f55,f55])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,conjecture,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f17])).

fof(f32,plain,(
    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,
    ( ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
   => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).

fof(f54,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f54,f56])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_409,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_407,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1019,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_409,c_407])).

cnf(c_1387,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_1,c_1019])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_398,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_555,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_409,c_398])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_556,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_555,c_9])).

cnf(c_1585,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_1387,c_556])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_399,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_604,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_409,c_399])).

cnf(c_10,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_403,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_763,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_403])).

cnf(c_52,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_886,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_763,c_52])).

cnf(c_892,plain,
    ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_556,c_886])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_405,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1078,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_405])).

cnf(c_1152,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1078,c_52])).

cnf(c_1153,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1152])).

cnf(c_1158,plain,
    ( r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_892,c_1153])).

cnf(c_1159,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1158,c_9])).

cnf(c_1164,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1159,c_52])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_410,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1170,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1164,c_410])).

cnf(c_1386,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_1170,c_1019])).

cnf(c_1590,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_1387,c_1019])).

cnf(c_1779,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X3),X2),X1) ),
    inference(superposition,[status(thm)],[c_1387,c_1590])).

cnf(c_893,plain,
    ( k1_setfam_1(k2_enumset1(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_886,c_410])).

cnf(c_1389,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_1019,c_556])).

cnf(c_2271,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_1,c_1389])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2342,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_2271,c_8])).

cnf(c_2358,plain,
    ( k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2342,c_1585])).

cnf(c_2496,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_2358,c_8])).

cnf(c_4846,plain,
    ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_893,c_2496])).

cnf(c_4848,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)))),k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_893,c_2271])).

cnf(c_4856,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_4846,c_4848])).

cnf(c_4857,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_4856,c_556])).

cnf(c_5295,plain,
    ( k6_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1387,c_4857])).

cnf(c_5296,plain,
    ( k6_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1019,c_4857])).

cnf(c_5360,plain,
    ( k7_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k6_relat_1(X0)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_5296,c_1387])).

cnf(c_5361,plain,
    ( k6_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(demodulation,[status(thm)],[c_5295,c_5360])).

cnf(c_5362,plain,
    ( k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_5361,c_1387])).

cnf(c_5787,plain,
    ( k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_5362,c_9])).

cnf(c_5928,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3) = k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1),X3))) ),
    inference(superposition,[status(thm)],[c_1779,c_5787])).

cnf(c_5934,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X3),X1))) ),
    inference(superposition,[status(thm)],[c_1019,c_5787])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_408,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_709,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_408])).

cnf(c_4849,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_893,c_709])).

cnf(c_4955,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4849,c_52])).

cnf(c_4974,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
    inference(superposition,[status(thm)],[c_4955,c_407])).

cnf(c_5952,plain,
    ( k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X3),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_5934,c_4974])).

cnf(c_5958,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X3),X2),X1) ),
    inference(demodulation,[status(thm)],[c_5928,c_5952])).

cnf(c_5959,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X3),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_5958,c_1387])).

cnf(c_6899,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_1386,c_5959])).

cnf(c_7015,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0) ),
    inference(superposition,[status(thm)],[c_1585,c_6899])).

cnf(c_7069,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_7015,c_1389])).

cnf(c_7016,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ),
    inference(superposition,[status(thm)],[c_2271,c_6899])).

cnf(c_7070,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ),
    inference(demodulation,[status(thm)],[c_7069,c_7016])).

cnf(c_11,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_402,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_764,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_402])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_406,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_400,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1098,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X1))) = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_406,c_400])).

cnf(c_39578,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k6_relat_1(X1)))) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_764,c_1098])).

cnf(c_39622,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_39578,c_8])).

cnf(c_40396,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39622,c_52,c_4849])).

cnf(c_40402,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_409,c_40396])).

cnf(c_41038,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ),
    inference(superposition,[status(thm)],[c_7070,c_40402])).

cnf(c_7013,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) ),
    inference(superposition,[status(thm)],[c_1389,c_6899])).

cnf(c_7071,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_7013,c_1585])).

cnf(c_41182,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ),
    inference(light_normalisation,[status(thm)],[c_41038,c_7071])).

cnf(c_1778,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_556,c_1590])).

cnf(c_2337,plain,
    ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_2271,c_604])).

cnf(c_2363,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_2337,c_1585])).

cnf(c_2364,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_2363,c_604,c_1387])).

cnf(c_2993,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_2364])).

cnf(c_41183,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_41182,c_1778,c_2993,c_7071])).

cnf(c_2311,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_2271,c_1590])).

cnf(c_8982,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(demodulation,[status(thm)],[c_7069,c_2311])).

cnf(c_41288,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_41183,c_8982])).

cnf(c_16,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_762,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_604,c_16])).

cnf(c_47819,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_41288,c_762])).

cnf(c_47888,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_47819])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 15.58/2.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.58/2.54  
% 15.58/2.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.58/2.54  
% 15.58/2.54  ------  iProver source info
% 15.58/2.54  
% 15.58/2.54  git: date: 2020-06-30 10:37:57 +0100
% 15.58/2.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.58/2.54  git: non_committed_changes: false
% 15.58/2.54  git: last_make_outside_of_git: false
% 15.58/2.54  
% 15.58/2.54  ------ 
% 15.58/2.54  
% 15.58/2.54  ------ Input Options
% 15.58/2.54  
% 15.58/2.54  --out_options                           all
% 15.58/2.54  --tptp_safe_out                         true
% 15.58/2.54  --problem_path                          ""
% 15.58/2.54  --include_path                          ""
% 15.58/2.54  --clausifier                            res/vclausify_rel
% 15.58/2.54  --clausifier_options                    ""
% 15.58/2.54  --stdin                                 false
% 15.58/2.54  --stats_out                             all
% 15.58/2.54  
% 15.58/2.54  ------ General Options
% 15.58/2.54  
% 15.58/2.54  --fof                                   false
% 15.58/2.54  --time_out_real                         305.
% 15.58/2.54  --time_out_virtual                      -1.
% 15.58/2.54  --symbol_type_check                     false
% 15.58/2.54  --clausify_out                          false
% 15.58/2.54  --sig_cnt_out                           false
% 15.58/2.54  --trig_cnt_out                          false
% 15.58/2.54  --trig_cnt_out_tolerance                1.
% 15.58/2.54  --trig_cnt_out_sk_spl                   false
% 15.58/2.54  --abstr_cl_out                          false
% 15.58/2.54  
% 15.58/2.54  ------ Global Options
% 15.58/2.54  
% 15.58/2.54  --schedule                              default
% 15.58/2.54  --add_important_lit                     false
% 15.58/2.54  --prop_solver_per_cl                    1000
% 15.58/2.54  --min_unsat_core                        false
% 15.58/2.54  --soft_assumptions                      false
% 15.58/2.54  --soft_lemma_size                       3
% 15.58/2.54  --prop_impl_unit_size                   0
% 15.58/2.54  --prop_impl_unit                        []
% 15.58/2.54  --share_sel_clauses                     true
% 15.58/2.54  --reset_solvers                         false
% 15.58/2.54  --bc_imp_inh                            [conj_cone]
% 15.58/2.54  --conj_cone_tolerance                   3.
% 15.58/2.54  --extra_neg_conj                        none
% 15.58/2.54  --large_theory_mode                     true
% 15.58/2.54  --prolific_symb_bound                   200
% 15.58/2.54  --lt_threshold                          2000
% 15.58/2.54  --clause_weak_htbl                      true
% 15.58/2.54  --gc_record_bc_elim                     false
% 15.58/2.54  
% 15.58/2.54  ------ Preprocessing Options
% 15.58/2.54  
% 15.58/2.54  --preprocessing_flag                    true
% 15.58/2.54  --time_out_prep_mult                    0.1
% 15.58/2.54  --splitting_mode                        input
% 15.58/2.54  --splitting_grd                         true
% 15.58/2.54  --splitting_cvd                         false
% 15.58/2.54  --splitting_cvd_svl                     false
% 15.58/2.54  --splitting_nvd                         32
% 15.58/2.54  --sub_typing                            true
% 15.58/2.54  --prep_gs_sim                           true
% 15.58/2.54  --prep_unflatten                        true
% 15.58/2.54  --prep_res_sim                          true
% 15.58/2.54  --prep_upred                            true
% 15.58/2.54  --prep_sem_filter                       exhaustive
% 15.58/2.54  --prep_sem_filter_out                   false
% 15.58/2.54  --pred_elim                             true
% 15.58/2.54  --res_sim_input                         true
% 15.58/2.54  --eq_ax_congr_red                       true
% 15.58/2.54  --pure_diseq_elim                       true
% 15.58/2.54  --brand_transform                       false
% 15.58/2.54  --non_eq_to_eq                          false
% 15.58/2.54  --prep_def_merge                        true
% 15.58/2.54  --prep_def_merge_prop_impl              false
% 15.58/2.54  --prep_def_merge_mbd                    true
% 15.58/2.54  --prep_def_merge_tr_red                 false
% 15.58/2.54  --prep_def_merge_tr_cl                  false
% 15.58/2.54  --smt_preprocessing                     true
% 15.58/2.54  --smt_ac_axioms                         fast
% 15.58/2.54  --preprocessed_out                      false
% 15.58/2.54  --preprocessed_stats                    false
% 15.58/2.54  
% 15.58/2.54  ------ Abstraction refinement Options
% 15.58/2.54  
% 15.58/2.54  --abstr_ref                             []
% 15.58/2.54  --abstr_ref_prep                        false
% 15.58/2.54  --abstr_ref_until_sat                   false
% 15.58/2.54  --abstr_ref_sig_restrict                funpre
% 15.58/2.54  --abstr_ref_af_restrict_to_split_sk     false
% 15.58/2.54  --abstr_ref_under                       []
% 15.58/2.54  
% 15.58/2.54  ------ SAT Options
% 15.58/2.54  
% 15.58/2.54  --sat_mode                              false
% 15.58/2.54  --sat_fm_restart_options                ""
% 15.58/2.54  --sat_gr_def                            false
% 15.58/2.54  --sat_epr_types                         true
% 15.58/2.54  --sat_non_cyclic_types                  false
% 15.58/2.54  --sat_finite_models                     false
% 15.58/2.54  --sat_fm_lemmas                         false
% 15.58/2.54  --sat_fm_prep                           false
% 15.58/2.54  --sat_fm_uc_incr                        true
% 15.58/2.54  --sat_out_model                         small
% 15.58/2.54  --sat_out_clauses                       false
% 15.58/2.54  
% 15.58/2.54  ------ QBF Options
% 15.58/2.54  
% 15.58/2.54  --qbf_mode                              false
% 15.58/2.54  --qbf_elim_univ                         false
% 15.58/2.54  --qbf_dom_inst                          none
% 15.58/2.54  --qbf_dom_pre_inst                      false
% 15.58/2.54  --qbf_sk_in                             false
% 15.58/2.54  --qbf_pred_elim                         true
% 15.58/2.54  --qbf_split                             512
% 15.58/2.54  
% 15.58/2.54  ------ BMC1 Options
% 15.58/2.54  
% 15.58/2.54  --bmc1_incremental                      false
% 15.58/2.54  --bmc1_axioms                           reachable_all
% 15.58/2.54  --bmc1_min_bound                        0
% 15.58/2.54  --bmc1_max_bound                        -1
% 15.58/2.54  --bmc1_max_bound_default                -1
% 15.58/2.54  --bmc1_symbol_reachability              true
% 15.58/2.54  --bmc1_property_lemmas                  false
% 15.58/2.54  --bmc1_k_induction                      false
% 15.58/2.54  --bmc1_non_equiv_states                 false
% 15.58/2.54  --bmc1_deadlock                         false
% 15.58/2.54  --bmc1_ucm                              false
% 15.58/2.54  --bmc1_add_unsat_core                   none
% 15.58/2.54  --bmc1_unsat_core_children              false
% 15.58/2.54  --bmc1_unsat_core_extrapolate_axioms    false
% 15.58/2.54  --bmc1_out_stat                         full
% 15.58/2.54  --bmc1_ground_init                      false
% 15.58/2.54  --bmc1_pre_inst_next_state              false
% 15.58/2.54  --bmc1_pre_inst_state                   false
% 15.58/2.54  --bmc1_pre_inst_reach_state             false
% 15.58/2.54  --bmc1_out_unsat_core                   false
% 15.58/2.54  --bmc1_aig_witness_out                  false
% 15.58/2.54  --bmc1_verbose                          false
% 15.58/2.54  --bmc1_dump_clauses_tptp                false
% 15.58/2.54  --bmc1_dump_unsat_core_tptp             false
% 15.58/2.54  --bmc1_dump_file                        -
% 15.58/2.54  --bmc1_ucm_expand_uc_limit              128
% 15.58/2.54  --bmc1_ucm_n_expand_iterations          6
% 15.58/2.54  --bmc1_ucm_extend_mode                  1
% 15.58/2.54  --bmc1_ucm_init_mode                    2
% 15.58/2.54  --bmc1_ucm_cone_mode                    none
% 15.58/2.54  --bmc1_ucm_reduced_relation_type        0
% 15.58/2.54  --bmc1_ucm_relax_model                  4
% 15.58/2.54  --bmc1_ucm_full_tr_after_sat            true
% 15.58/2.54  --bmc1_ucm_expand_neg_assumptions       false
% 15.58/2.54  --bmc1_ucm_layered_model                none
% 15.58/2.54  --bmc1_ucm_max_lemma_size               10
% 15.58/2.54  
% 15.58/2.54  ------ AIG Options
% 15.58/2.54  
% 15.58/2.54  --aig_mode                              false
% 15.58/2.54  
% 15.58/2.54  ------ Instantiation Options
% 15.58/2.54  
% 15.58/2.54  --instantiation_flag                    true
% 15.58/2.54  --inst_sos_flag                         true
% 15.58/2.54  --inst_sos_phase                        true
% 15.58/2.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.58/2.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.58/2.54  --inst_lit_sel_side                     num_symb
% 15.58/2.54  --inst_solver_per_active                1400
% 15.58/2.54  --inst_solver_calls_frac                1.
% 15.58/2.54  --inst_passive_queue_type               priority_queues
% 15.58/2.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.58/2.54  --inst_passive_queues_freq              [25;2]
% 15.58/2.54  --inst_dismatching                      true
% 15.58/2.54  --inst_eager_unprocessed_to_passive     true
% 15.58/2.54  --inst_prop_sim_given                   true
% 15.58/2.54  --inst_prop_sim_new                     false
% 15.58/2.54  --inst_subs_new                         false
% 15.58/2.54  --inst_eq_res_simp                      false
% 15.58/2.54  --inst_subs_given                       false
% 15.58/2.54  --inst_orphan_elimination               true
% 15.58/2.54  --inst_learning_loop_flag               true
% 15.58/2.54  --inst_learning_start                   3000
% 15.58/2.54  --inst_learning_factor                  2
% 15.58/2.54  --inst_start_prop_sim_after_learn       3
% 15.58/2.54  --inst_sel_renew                        solver
% 15.58/2.54  --inst_lit_activity_flag                true
% 15.58/2.54  --inst_restr_to_given                   false
% 15.58/2.54  --inst_activity_threshold               500
% 15.58/2.54  --inst_out_proof                        true
% 15.58/2.54  
% 15.58/2.54  ------ Resolution Options
% 15.58/2.54  
% 15.58/2.54  --resolution_flag                       true
% 15.58/2.54  --res_lit_sel                           adaptive
% 15.58/2.54  --res_lit_sel_side                      none
% 15.58/2.54  --res_ordering                          kbo
% 15.58/2.54  --res_to_prop_solver                    active
% 15.58/2.54  --res_prop_simpl_new                    false
% 15.58/2.54  --res_prop_simpl_given                  true
% 15.58/2.54  --res_passive_queue_type                priority_queues
% 15.58/2.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.58/2.54  --res_passive_queues_freq               [15;5]
% 15.58/2.54  --res_forward_subs                      full
% 15.58/2.54  --res_backward_subs                     full
% 15.58/2.54  --res_forward_subs_resolution           true
% 15.58/2.54  --res_backward_subs_resolution          true
% 15.58/2.54  --res_orphan_elimination                true
% 15.58/2.54  --res_time_limit                        2.
% 15.58/2.54  --res_out_proof                         true
% 15.58/2.54  
% 15.58/2.54  ------ Superposition Options
% 15.58/2.54  
% 15.58/2.54  --superposition_flag                    true
% 15.58/2.54  --sup_passive_queue_type                priority_queues
% 15.58/2.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.58/2.54  --sup_passive_queues_freq               [8;1;4]
% 15.58/2.54  --demod_completeness_check              fast
% 15.58/2.54  --demod_use_ground                      true
% 15.58/2.54  --sup_to_prop_solver                    passive
% 15.58/2.54  --sup_prop_simpl_new                    true
% 15.58/2.54  --sup_prop_simpl_given                  true
% 15.58/2.54  --sup_fun_splitting                     true
% 15.58/2.54  --sup_smt_interval                      50000
% 15.58/2.54  
% 15.58/2.54  ------ Superposition Simplification Setup
% 15.58/2.54  
% 15.58/2.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.58/2.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.58/2.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.58/2.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.58/2.54  --sup_full_triv                         [TrivRules;PropSubs]
% 15.58/2.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.58/2.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.58/2.54  --sup_immed_triv                        [TrivRules]
% 15.58/2.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.54  --sup_immed_bw_main                     []
% 15.58/2.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.58/2.54  --sup_input_triv                        [Unflattening;TrivRules]
% 15.58/2.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.54  --sup_input_bw                          []
% 15.58/2.54  
% 15.58/2.54  ------ Combination Options
% 15.58/2.54  
% 15.58/2.54  --comb_res_mult                         3
% 15.58/2.54  --comb_sup_mult                         2
% 15.58/2.54  --comb_inst_mult                        10
% 15.58/2.54  
% 15.58/2.54  ------ Debug Options
% 15.58/2.54  
% 15.58/2.54  --dbg_backtrace                         false
% 15.58/2.54  --dbg_dump_prop_clauses                 false
% 15.58/2.54  --dbg_dump_prop_clauses_file            -
% 15.58/2.54  --dbg_out_stat                          false
% 15.58/2.54  ------ Parsing...
% 15.58/2.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.58/2.54  
% 15.58/2.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.58/2.54  
% 15.58/2.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.58/2.54  
% 15.58/2.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.58/2.54  ------ Proving...
% 15.58/2.54  ------ Problem Properties 
% 15.58/2.54  
% 15.58/2.54  
% 15.58/2.54  clauses                                 17
% 15.58/2.54  conjectures                             1
% 15.58/2.54  EPR                                     0
% 15.58/2.54  Horn                                    17
% 15.58/2.54  unary                                   5
% 15.58/2.54  binary                                  7
% 15.58/2.54  lits                                    37
% 15.58/2.54  lits eq                                 11
% 15.58/2.54  fd_pure                                 0
% 15.58/2.54  fd_pseudo                               0
% 15.58/2.54  fd_cond                                 0
% 15.58/2.54  fd_pseudo_cond                          0
% 15.58/2.54  AC symbols                              0
% 15.58/2.54  
% 15.58/2.54  ------ Schedule dynamic 5 is on 
% 15.58/2.54  
% 15.58/2.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.58/2.54  
% 15.58/2.54  
% 15.58/2.54  ------ 
% 15.58/2.54  Current options:
% 15.58/2.54  ------ 
% 15.58/2.54  
% 15.58/2.54  ------ Input Options
% 15.58/2.54  
% 15.58/2.54  --out_options                           all
% 15.58/2.54  --tptp_safe_out                         true
% 15.58/2.54  --problem_path                          ""
% 15.58/2.54  --include_path                          ""
% 15.58/2.54  --clausifier                            res/vclausify_rel
% 15.58/2.54  --clausifier_options                    ""
% 15.58/2.54  --stdin                                 false
% 15.58/2.54  --stats_out                             all
% 15.58/2.54  
% 15.58/2.54  ------ General Options
% 15.58/2.54  
% 15.58/2.54  --fof                                   false
% 15.58/2.54  --time_out_real                         305.
% 15.58/2.54  --time_out_virtual                      -1.
% 15.58/2.54  --symbol_type_check                     false
% 15.58/2.54  --clausify_out                          false
% 15.58/2.54  --sig_cnt_out                           false
% 15.58/2.54  --trig_cnt_out                          false
% 15.58/2.54  --trig_cnt_out_tolerance                1.
% 15.58/2.54  --trig_cnt_out_sk_spl                   false
% 15.58/2.54  --abstr_cl_out                          false
% 15.58/2.54  
% 15.58/2.54  ------ Global Options
% 15.58/2.54  
% 15.58/2.54  --schedule                              default
% 15.58/2.54  --add_important_lit                     false
% 15.58/2.54  --prop_solver_per_cl                    1000
% 15.58/2.54  --min_unsat_core                        false
% 15.58/2.54  --soft_assumptions                      false
% 15.58/2.54  --soft_lemma_size                       3
% 15.58/2.54  --prop_impl_unit_size                   0
% 15.58/2.54  --prop_impl_unit                        []
% 15.58/2.54  --share_sel_clauses                     true
% 15.58/2.54  --reset_solvers                         false
% 15.58/2.54  --bc_imp_inh                            [conj_cone]
% 15.58/2.54  --conj_cone_tolerance                   3.
% 15.58/2.54  --extra_neg_conj                        none
% 15.58/2.54  --large_theory_mode                     true
% 15.58/2.54  --prolific_symb_bound                   200
% 15.58/2.54  --lt_threshold                          2000
% 15.58/2.54  --clause_weak_htbl                      true
% 15.58/2.54  --gc_record_bc_elim                     false
% 15.58/2.54  
% 15.58/2.54  ------ Preprocessing Options
% 15.58/2.54  
% 15.58/2.54  --preprocessing_flag                    true
% 15.58/2.54  --time_out_prep_mult                    0.1
% 15.58/2.54  --splitting_mode                        input
% 15.58/2.54  --splitting_grd                         true
% 15.58/2.54  --splitting_cvd                         false
% 15.58/2.54  --splitting_cvd_svl                     false
% 15.58/2.54  --splitting_nvd                         32
% 15.58/2.54  --sub_typing                            true
% 15.58/2.54  --prep_gs_sim                           true
% 15.58/2.54  --prep_unflatten                        true
% 15.58/2.54  --prep_res_sim                          true
% 15.58/2.54  --prep_upred                            true
% 15.58/2.54  --prep_sem_filter                       exhaustive
% 15.58/2.54  --prep_sem_filter_out                   false
% 15.58/2.54  --pred_elim                             true
% 15.58/2.54  --res_sim_input                         true
% 15.58/2.54  --eq_ax_congr_red                       true
% 15.58/2.54  --pure_diseq_elim                       true
% 15.58/2.54  --brand_transform                       false
% 15.58/2.54  --non_eq_to_eq                          false
% 15.58/2.54  --prep_def_merge                        true
% 15.58/2.54  --prep_def_merge_prop_impl              false
% 15.58/2.54  --prep_def_merge_mbd                    true
% 15.58/2.54  --prep_def_merge_tr_red                 false
% 15.58/2.54  --prep_def_merge_tr_cl                  false
% 15.58/2.54  --smt_preprocessing                     true
% 15.58/2.54  --smt_ac_axioms                         fast
% 15.58/2.54  --preprocessed_out                      false
% 15.58/2.54  --preprocessed_stats                    false
% 15.58/2.54  
% 15.58/2.54  ------ Abstraction refinement Options
% 15.58/2.54  
% 15.58/2.54  --abstr_ref                             []
% 15.58/2.54  --abstr_ref_prep                        false
% 15.58/2.54  --abstr_ref_until_sat                   false
% 15.58/2.54  --abstr_ref_sig_restrict                funpre
% 15.58/2.54  --abstr_ref_af_restrict_to_split_sk     false
% 15.58/2.54  --abstr_ref_under                       []
% 15.58/2.54  
% 15.58/2.54  ------ SAT Options
% 15.58/2.54  
% 15.58/2.54  --sat_mode                              false
% 15.58/2.54  --sat_fm_restart_options                ""
% 15.58/2.54  --sat_gr_def                            false
% 15.58/2.54  --sat_epr_types                         true
% 15.58/2.54  --sat_non_cyclic_types                  false
% 15.58/2.54  --sat_finite_models                     false
% 15.58/2.54  --sat_fm_lemmas                         false
% 15.58/2.54  --sat_fm_prep                           false
% 15.58/2.54  --sat_fm_uc_incr                        true
% 15.58/2.54  --sat_out_model                         small
% 15.58/2.54  --sat_out_clauses                       false
% 15.58/2.54  
% 15.58/2.54  ------ QBF Options
% 15.58/2.54  
% 15.58/2.54  --qbf_mode                              false
% 15.58/2.54  --qbf_elim_univ                         false
% 15.58/2.54  --qbf_dom_inst                          none
% 15.58/2.54  --qbf_dom_pre_inst                      false
% 15.58/2.54  --qbf_sk_in                             false
% 15.58/2.54  --qbf_pred_elim                         true
% 15.58/2.54  --qbf_split                             512
% 15.58/2.54  
% 15.58/2.54  ------ BMC1 Options
% 15.58/2.54  
% 15.58/2.54  --bmc1_incremental                      false
% 15.58/2.54  --bmc1_axioms                           reachable_all
% 15.58/2.54  --bmc1_min_bound                        0
% 15.58/2.54  --bmc1_max_bound                        -1
% 15.58/2.54  --bmc1_max_bound_default                -1
% 15.58/2.54  --bmc1_symbol_reachability              true
% 15.58/2.54  --bmc1_property_lemmas                  false
% 15.58/2.54  --bmc1_k_induction                      false
% 15.58/2.54  --bmc1_non_equiv_states                 false
% 15.58/2.54  --bmc1_deadlock                         false
% 15.58/2.54  --bmc1_ucm                              false
% 15.58/2.54  --bmc1_add_unsat_core                   none
% 15.58/2.54  --bmc1_unsat_core_children              false
% 15.58/2.54  --bmc1_unsat_core_extrapolate_axioms    false
% 15.58/2.54  --bmc1_out_stat                         full
% 15.58/2.54  --bmc1_ground_init                      false
% 15.58/2.54  --bmc1_pre_inst_next_state              false
% 15.58/2.54  --bmc1_pre_inst_state                   false
% 15.58/2.54  --bmc1_pre_inst_reach_state             false
% 15.58/2.54  --bmc1_out_unsat_core                   false
% 15.58/2.54  --bmc1_aig_witness_out                  false
% 15.58/2.54  --bmc1_verbose                          false
% 15.58/2.54  --bmc1_dump_clauses_tptp                false
% 15.58/2.54  --bmc1_dump_unsat_core_tptp             false
% 15.58/2.54  --bmc1_dump_file                        -
% 15.58/2.54  --bmc1_ucm_expand_uc_limit              128
% 15.58/2.54  --bmc1_ucm_n_expand_iterations          6
% 15.58/2.54  --bmc1_ucm_extend_mode                  1
% 15.58/2.54  --bmc1_ucm_init_mode                    2
% 15.58/2.54  --bmc1_ucm_cone_mode                    none
% 15.58/2.54  --bmc1_ucm_reduced_relation_type        0
% 15.58/2.54  --bmc1_ucm_relax_model                  4
% 15.58/2.54  --bmc1_ucm_full_tr_after_sat            true
% 15.58/2.54  --bmc1_ucm_expand_neg_assumptions       false
% 15.58/2.54  --bmc1_ucm_layered_model                none
% 15.58/2.54  --bmc1_ucm_max_lemma_size               10
% 15.58/2.54  
% 15.58/2.54  ------ AIG Options
% 15.58/2.54  
% 15.58/2.54  --aig_mode                              false
% 15.58/2.54  
% 15.58/2.54  ------ Instantiation Options
% 15.58/2.54  
% 15.58/2.54  --instantiation_flag                    true
% 15.58/2.54  --inst_sos_flag                         true
% 15.58/2.54  --inst_sos_phase                        true
% 15.58/2.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.58/2.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.58/2.54  --inst_lit_sel_side                     none
% 15.58/2.54  --inst_solver_per_active                1400
% 15.58/2.54  --inst_solver_calls_frac                1.
% 15.58/2.54  --inst_passive_queue_type               priority_queues
% 15.58/2.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.58/2.54  --inst_passive_queues_freq              [25;2]
% 15.58/2.54  --inst_dismatching                      true
% 15.58/2.54  --inst_eager_unprocessed_to_passive     true
% 15.58/2.54  --inst_prop_sim_given                   true
% 15.58/2.54  --inst_prop_sim_new                     false
% 15.58/2.54  --inst_subs_new                         false
% 15.58/2.54  --inst_eq_res_simp                      false
% 15.58/2.54  --inst_subs_given                       false
% 15.58/2.54  --inst_orphan_elimination               true
% 15.58/2.54  --inst_learning_loop_flag               true
% 15.58/2.54  --inst_learning_start                   3000
% 15.58/2.54  --inst_learning_factor                  2
% 15.58/2.54  --inst_start_prop_sim_after_learn       3
% 15.58/2.54  --inst_sel_renew                        solver
% 15.58/2.54  --inst_lit_activity_flag                true
% 15.58/2.54  --inst_restr_to_given                   false
% 15.58/2.54  --inst_activity_threshold               500
% 15.58/2.54  --inst_out_proof                        true
% 15.58/2.54  
% 15.58/2.54  ------ Resolution Options
% 15.58/2.54  
% 15.58/2.54  --resolution_flag                       false
% 15.58/2.54  --res_lit_sel                           adaptive
% 15.58/2.54  --res_lit_sel_side                      none
% 15.58/2.54  --res_ordering                          kbo
% 15.58/2.54  --res_to_prop_solver                    active
% 15.58/2.54  --res_prop_simpl_new                    false
% 15.58/2.54  --res_prop_simpl_given                  true
% 15.58/2.54  --res_passive_queue_type                priority_queues
% 15.58/2.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.58/2.54  --res_passive_queues_freq               [15;5]
% 15.58/2.54  --res_forward_subs                      full
% 15.58/2.54  --res_backward_subs                     full
% 15.58/2.54  --res_forward_subs_resolution           true
% 15.58/2.54  --res_backward_subs_resolution          true
% 15.58/2.54  --res_orphan_elimination                true
% 15.58/2.54  --res_time_limit                        2.
% 15.58/2.54  --res_out_proof                         true
% 15.58/2.54  
% 15.58/2.54  ------ Superposition Options
% 15.58/2.54  
% 15.58/2.54  --superposition_flag                    true
% 15.58/2.54  --sup_passive_queue_type                priority_queues
% 15.58/2.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.58/2.54  --sup_passive_queues_freq               [8;1;4]
% 15.58/2.54  --demod_completeness_check              fast
% 15.58/2.54  --demod_use_ground                      true
% 15.58/2.54  --sup_to_prop_solver                    passive
% 15.58/2.54  --sup_prop_simpl_new                    true
% 15.58/2.54  --sup_prop_simpl_given                  true
% 15.58/2.54  --sup_fun_splitting                     true
% 15.58/2.54  --sup_smt_interval                      50000
% 15.58/2.54  
% 15.58/2.54  ------ Superposition Simplification Setup
% 15.58/2.54  
% 15.58/2.54  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.58/2.54  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.58/2.54  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.58/2.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.58/2.54  --sup_full_triv                         [TrivRules;PropSubs]
% 15.58/2.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.58/2.54  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.58/2.54  --sup_immed_triv                        [TrivRules]
% 15.58/2.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.54  --sup_immed_bw_main                     []
% 15.58/2.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.58/2.54  --sup_input_triv                        [Unflattening;TrivRules]
% 15.58/2.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.58/2.54  --sup_input_bw                          []
% 15.58/2.54  
% 15.58/2.54  ------ Combination Options
% 15.58/2.54  
% 15.58/2.54  --comb_res_mult                         3
% 15.58/2.54  --comb_sup_mult                         2
% 15.58/2.54  --comb_inst_mult                        10
% 15.58/2.54  
% 15.58/2.54  ------ Debug Options
% 15.58/2.54  
% 15.58/2.54  --dbg_backtrace                         false
% 15.58/2.54  --dbg_dump_prop_clauses                 false
% 15.58/2.54  --dbg_dump_prop_clauses_file            -
% 15.58/2.54  --dbg_out_stat                          false
% 15.58/2.54  
% 15.58/2.54  
% 15.58/2.54  
% 15.58/2.54  
% 15.58/2.54  ------ Proving...
% 15.58/2.54  
% 15.58/2.54  
% 15.58/2.54  % SZS status Theorem for theBenchmark.p
% 15.58/2.54  
% 15.58/2.54   Resolution empty clause
% 15.58/2.54  
% 15.58/2.54  % SZS output start CNFRefutation for theBenchmark.p
% 15.58/2.54  
% 15.58/2.54  fof(f2,axiom,(
% 15.58/2.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 15.58/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.54  
% 15.58/2.54  fof(f36,plain,(
% 15.58/2.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 15.58/2.54    inference(cnf_transformation,[],[f2])).
% 15.58/2.54  
% 15.58/2.54  fof(f3,axiom,(
% 15.58/2.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.58/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.54  
% 15.58/2.54  fof(f37,plain,(
% 15.58/2.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.58/2.54    inference(cnf_transformation,[],[f3])).
% 15.58/2.54  
% 15.58/2.54  fof(f4,axiom,(
% 15.58/2.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.58/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.54  
% 15.58/2.54  fof(f38,plain,(
% 15.58/2.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.58/2.54    inference(cnf_transformation,[],[f4])).
% 15.58/2.54  
% 15.58/2.54  fof(f55,plain,(
% 15.58/2.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 15.58/2.54    inference(definition_unfolding,[],[f37,f38])).
% 15.58/2.54  
% 15.58/2.54  fof(f58,plain,(
% 15.58/2.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 15.58/2.54    inference(definition_unfolding,[],[f36,f55,f55])).
% 15.58/2.54  
% 15.58/2.54  fof(f6,axiom,(
% 15.58/2.54    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 15.58/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.54  
% 15.58/2.54  fof(f40,plain,(
% 15.58/2.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 15.58/2.54    inference(cnf_transformation,[],[f6])).
% 15.58/2.54  
% 15.58/2.54  fof(f8,axiom,(
% 15.58/2.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 15.58/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.54  
% 15.58/2.54  fof(f21,plain,(
% 15.58/2.54    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 15.58/2.54    inference(ennf_transformation,[],[f8])).
% 15.58/2.54  
% 15.58/2.54  fof(f42,plain,(
% 15.58/2.54    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 15.58/2.54    inference(cnf_transformation,[],[f21])).
% 15.58/2.54  
% 15.58/2.54  fof(f5,axiom,(
% 15.58/2.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.58/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.54  
% 15.58/2.54  fof(f39,plain,(
% 15.58/2.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.58/2.54    inference(cnf_transformation,[],[f5])).
% 15.58/2.54  
% 15.58/2.54  fof(f56,plain,(
% 15.58/2.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 15.58/2.54    inference(definition_unfolding,[],[f39,f55])).
% 15.58/2.54  
% 15.58/2.54  fof(f60,plain,(
% 15.58/2.54    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 15.58/2.54    inference(definition_unfolding,[],[f42,f56])).
% 15.58/2.54  
% 15.58/2.54  fof(f16,axiom,(
% 15.58/2.54    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 15.58/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.54  
% 15.58/2.54  fof(f31,plain,(
% 15.58/2.54    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 15.58/2.54    inference(ennf_transformation,[],[f16])).
% 15.58/2.54  
% 15.58/2.54  fof(f53,plain,(
% 15.58/2.54    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 15.58/2.54    inference(cnf_transformation,[],[f31])).
% 15.58/2.54  
% 15.58/2.54  fof(f11,axiom,(
% 15.58/2.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 15.58/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.54  
% 15.58/2.54  fof(f46,plain,(
% 15.58/2.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 15.58/2.54    inference(cnf_transformation,[],[f11])).
% 15.58/2.54  
% 15.58/2.54  fof(f15,axiom,(
% 15.58/2.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 15.58/2.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.54  
% 15.58/2.54  fof(f30,plain,(
% 15.58/2.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 15.58/2.55    inference(ennf_transformation,[],[f15])).
% 15.58/2.55  
% 15.58/2.55  fof(f52,plain,(
% 15.58/2.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 15.58/2.55    inference(cnf_transformation,[],[f30])).
% 15.58/2.55  
% 15.58/2.55  fof(f12,axiom,(
% 15.58/2.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 15.58/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.55  
% 15.58/2.55  fof(f25,plain,(
% 15.58/2.55    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 15.58/2.55    inference(ennf_transformation,[],[f12])).
% 15.58/2.55  
% 15.58/2.55  fof(f49,plain,(
% 15.58/2.55    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 15.58/2.55    inference(cnf_transformation,[],[f25])).
% 15.58/2.55  
% 15.58/2.55  fof(f9,axiom,(
% 15.58/2.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 15.58/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.55  
% 15.58/2.55  fof(f22,plain,(
% 15.58/2.55    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.58/2.55    inference(ennf_transformation,[],[f9])).
% 15.58/2.55  
% 15.58/2.55  fof(f23,plain,(
% 15.58/2.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.58/2.55    inference(flattening,[],[f22])).
% 15.58/2.55  
% 15.58/2.55  fof(f43,plain,(
% 15.58/2.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.58/2.55    inference(cnf_transformation,[],[f23])).
% 15.58/2.55  
% 15.58/2.55  fof(f1,axiom,(
% 15.58/2.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.58/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.55  
% 15.58/2.55  fof(f19,plain,(
% 15.58/2.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.58/2.55    inference(ennf_transformation,[],[f1])).
% 15.58/2.55  
% 15.58/2.55  fof(f35,plain,(
% 15.58/2.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.58/2.55    inference(cnf_transformation,[],[f19])).
% 15.58/2.55  
% 15.58/2.55  fof(f57,plain,(
% 15.58/2.55    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 15.58/2.55    inference(definition_unfolding,[],[f35,f56])).
% 15.58/2.55  
% 15.58/2.55  fof(f47,plain,(
% 15.58/2.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 15.58/2.55    inference(cnf_transformation,[],[f11])).
% 15.58/2.55  
% 15.58/2.55  fof(f7,axiom,(
% 15.58/2.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 15.58/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.55  
% 15.58/2.55  fof(f20,plain,(
% 15.58/2.55    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 15.58/2.55    inference(ennf_transformation,[],[f7])).
% 15.58/2.55  
% 15.58/2.55  fof(f41,plain,(
% 15.58/2.55    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 15.58/2.55    inference(cnf_transformation,[],[f20])).
% 15.58/2.55  
% 15.58/2.55  fof(f59,plain,(
% 15.58/2.55    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 15.58/2.55    inference(definition_unfolding,[],[f41,f56])).
% 15.58/2.55  
% 15.58/2.55  fof(f48,plain,(
% 15.58/2.55    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 15.58/2.55    inference(cnf_transformation,[],[f25])).
% 15.58/2.55  
% 15.58/2.55  fof(f44,plain,(
% 15.58/2.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.58/2.55    inference(cnf_transformation,[],[f23])).
% 15.58/2.55  
% 15.58/2.55  fof(f14,axiom,(
% 15.58/2.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 15.58/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.55  
% 15.58/2.55  fof(f28,plain,(
% 15.58/2.55    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.58/2.55    inference(ennf_transformation,[],[f14])).
% 15.58/2.55  
% 15.58/2.55  fof(f29,plain,(
% 15.58/2.55    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 15.58/2.55    inference(flattening,[],[f28])).
% 15.58/2.55  
% 15.58/2.55  fof(f51,plain,(
% 15.58/2.55    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 15.58/2.55    inference(cnf_transformation,[],[f29])).
% 15.58/2.55  
% 15.58/2.55  fof(f17,conjecture,(
% 15.58/2.55    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 15.58/2.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.58/2.55  
% 15.58/2.55  fof(f18,negated_conjecture,(
% 15.58/2.55    ~! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 15.58/2.55    inference(negated_conjecture,[],[f17])).
% 15.58/2.55  
% 15.58/2.55  fof(f32,plain,(
% 15.58/2.55    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 15.58/2.55    inference(ennf_transformation,[],[f18])).
% 15.58/2.55  
% 15.58/2.55  fof(f33,plain,(
% 15.58/2.55    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 15.58/2.55    introduced(choice_axiom,[])).
% 15.58/2.55  
% 15.58/2.55  fof(f34,plain,(
% 15.58/2.55    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 15.58/2.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).
% 15.58/2.55  
% 15.58/2.55  fof(f54,plain,(
% 15.58/2.55    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 15.58/2.55    inference(cnf_transformation,[],[f34])).
% 15.58/2.55  
% 15.58/2.55  fof(f61,plain,(
% 15.58/2.55    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 15.58/2.55    inference(definition_unfolding,[],[f54,f56])).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1,plain,
% 15.58/2.55      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 15.58/2.55      inference(cnf_transformation,[],[f58]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_2,plain,
% 15.58/2.55      ( v1_relat_1(k6_relat_1(X0)) ),
% 15.58/2.55      inference(cnf_transformation,[],[f40]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_409,plain,
% 15.58/2.55      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_4,plain,
% 15.58/2.55      ( ~ v1_relat_1(X0)
% 15.58/2.55      | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 15.58/2.55      inference(cnf_transformation,[],[f60]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_407,plain,
% 15.58/2.55      ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 15.58/2.55      | v1_relat_1(X0) != iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1019,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_409,c_407]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1387,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1,c_1019]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_15,plain,
% 15.58/2.55      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 15.58/2.55      inference(cnf_transformation,[],[f53]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_398,plain,
% 15.58/2.55      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_555,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_409,c_398]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_9,plain,
% 15.58/2.55      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 15.58/2.55      inference(cnf_transformation,[],[f46]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_556,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_555,c_9]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1585,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1387,c_556]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_14,plain,
% 15.58/2.55      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 15.58/2.55      inference(cnf_transformation,[],[f52]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_399,plain,
% 15.58/2.55      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 15.58/2.55      | v1_relat_1(X1) != iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_604,plain,
% 15.58/2.55      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_409,c_399]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_10,plain,
% 15.58/2.55      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~ v1_relat_1(X1) ),
% 15.58/2.55      inference(cnf_transformation,[],[f49]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_403,plain,
% 15.58/2.55      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
% 15.58/2.55      | v1_relat_1(X1) != iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_763,plain,
% 15.58/2.55      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
% 15.58/2.55      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_604,c_403]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_52,plain,
% 15.58/2.55      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_886,plain,
% 15.58/2.55      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
% 15.58/2.55      inference(global_propositional_subsumption,[status(thm)],[c_763,c_52]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_892,plain,
% 15.58/2.55      ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) = iProver_top ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_556,c_886]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_6,plain,
% 15.58/2.55      ( ~ r1_tarski(X0,X1)
% 15.58/2.55      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 15.58/2.55      | ~ v1_relat_1(X0)
% 15.58/2.55      | ~ v1_relat_1(X1) ),
% 15.58/2.55      inference(cnf_transformation,[],[f43]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_405,plain,
% 15.58/2.55      ( r1_tarski(X0,X1) != iProver_top
% 15.58/2.55      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 15.58/2.55      | v1_relat_1(X0) != iProver_top
% 15.58/2.55      | v1_relat_1(X1) != iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1078,plain,
% 15.58/2.55      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 15.58/2.55      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 15.58/2.55      | v1_relat_1(X1) != iProver_top
% 15.58/2.55      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_9,c_405]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1152,plain,
% 15.58/2.55      ( v1_relat_1(X1) != iProver_top
% 15.58/2.55      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 15.58/2.55      | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
% 15.58/2.55      inference(global_propositional_subsumption,[status(thm)],[c_1078,c_52]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1153,plain,
% 15.58/2.55      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 15.58/2.55      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 15.58/2.55      | v1_relat_1(X1) != iProver_top ),
% 15.58/2.55      inference(renaming,[status(thm)],[c_1152]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1158,plain,
% 15.58/2.55      ( r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) = iProver_top
% 15.58/2.55      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_892,c_1153]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1159,plain,
% 15.58/2.55      ( r1_tarski(X0,X0) = iProver_top
% 15.58/2.55      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_1158,c_9]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1164,plain,
% 15.58/2.55      ( r1_tarski(X0,X0) = iProver_top ),
% 15.58/2.55      inference(global_propositional_subsumption,[status(thm)],[c_1159,c_52]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_0,plain,
% 15.58/2.55      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
% 15.58/2.55      inference(cnf_transformation,[],[f57]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_410,plain,
% 15.58/2.55      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
% 15.58/2.55      | r1_tarski(X0,X1) != iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1170,plain,
% 15.58/2.55      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1164,c_410]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1386,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1170,c_1019]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1590,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1387,c_1019]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1779,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X3),X2),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1387,c_1590]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_893,plain,
% 15.58/2.55      ( k1_setfam_1(k2_enumset1(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_886,c_410]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1389,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1019,c_556]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_2271,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1,c_1389]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_8,plain,
% 15.58/2.55      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 15.58/2.55      inference(cnf_transformation,[],[f47]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_2342,plain,
% 15.58/2.55      ( k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_2271,c_8]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_2358,plain,
% 15.58/2.55      ( k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_2342,c_1585]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_2496,plain,
% 15.58/2.55      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_2358,c_8]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_4846,plain,
% 15.58/2.55      ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_893,c_2496]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_4848,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)))),k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_893,c_2271]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_4856,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_4846,c_4848]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_4857,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_4856,c_556]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5295,plain,
% 15.58/2.55      ( k6_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)),k6_relat_1(X0)) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1387,c_4857]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5296,plain,
% 15.58/2.55      ( k6_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k6_relat_1(X0)) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1019,c_4857]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5360,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k6_relat_1(X0)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_5296,c_1387]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5361,plain,
% 15.58/2.55      ( k6_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_5295,c_5360]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5362,plain,
% 15.58/2.55      ( k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_5361,c_1387]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5787,plain,
% 15.58/2.55      ( k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_5362,c_9]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5928,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3) = k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1),X3))) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1779,c_5787]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5934,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X3),X1))) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1019,c_5787]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_3,plain,
% 15.58/2.55      ( ~ v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 15.58/2.55      inference(cnf_transformation,[],[f59]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_408,plain,
% 15.58/2.55      ( v1_relat_1(X0) != iProver_top
% 15.58/2.55      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_709,plain,
% 15.58/2.55      ( v1_relat_1(X0) != iProver_top
% 15.58/2.55      | v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = iProver_top ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1,c_408]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_4849,plain,
% 15.58/2.55      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 15.58/2.55      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_893,c_709]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_4955,plain,
% 15.58/2.55      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 15.58/2.55      inference(global_propositional_subsumption,[status(thm)],[c_4849,c_52]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_4974,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_4955,c_407]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5952,plain,
% 15.58/2.55      ( k1_relat_1(k6_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X3),X1),X2) ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_5934,c_4974]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5958,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X3),X2),X1) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_5928,c_5952]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5959,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X3),X1),X2) ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_5958,c_1387]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_6899,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1386,c_5959]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_7015,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1585,c_6899]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_7069,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_7015,c_1389]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_7016,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_2271,c_6899]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_7070,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_7069,c_7016]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_11,plain,
% 15.58/2.55      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 15.58/2.55      inference(cnf_transformation,[],[f48]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_402,plain,
% 15.58/2.55      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
% 15.58/2.55      | v1_relat_1(X0) != iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_764,plain,
% 15.58/2.55      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
% 15.58/2.55      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_604,c_402]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_5,plain,
% 15.58/2.55      ( ~ r1_tarski(X0,X1)
% 15.58/2.55      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 15.58/2.55      | ~ v1_relat_1(X0)
% 15.58/2.55      | ~ v1_relat_1(X1) ),
% 15.58/2.55      inference(cnf_transformation,[],[f44]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_406,plain,
% 15.58/2.55      ( r1_tarski(X0,X1) != iProver_top
% 15.58/2.55      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 15.58/2.55      | v1_relat_1(X0) != iProver_top
% 15.58/2.55      | v1_relat_1(X1) != iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_13,plain,
% 15.58/2.55      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 15.58/2.55      | ~ v1_relat_1(X0)
% 15.58/2.55      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 15.58/2.55      inference(cnf_transformation,[],[f51]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_400,plain,
% 15.58/2.55      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 15.58/2.55      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 15.58/2.55      | v1_relat_1(X0) != iProver_top ),
% 15.58/2.55      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1098,plain,
% 15.58/2.55      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X1))) = X0
% 15.58/2.55      | r1_tarski(X0,X1) != iProver_top
% 15.58/2.55      | v1_relat_1(X0) != iProver_top
% 15.58/2.55      | v1_relat_1(X1) != iProver_top ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_406,c_400]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_39578,plain,
% 15.58/2.55      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k6_relat_1(X1)))) = k7_relat_1(k6_relat_1(X0),X1)
% 15.58/2.55      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 15.58/2.55      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_764,c_1098]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_39622,plain,
% 15.58/2.55      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
% 15.58/2.55      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 15.58/2.55      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_39578,c_8]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_40396,plain,
% 15.58/2.55      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
% 15.58/2.55      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 15.58/2.55      inference(global_propositional_subsumption,
% 15.58/2.55                [status(thm)],
% 15.58/2.55                [c_39622,c_52,c_4849]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_40402,plain,
% 15.58/2.55      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_409,c_40396]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_41038,plain,
% 15.58/2.55      ( k5_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_7070,c_40402]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_7013,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1389,c_6899]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_7071,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_7013,c_1585]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_41182,plain,
% 15.58/2.55      ( k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_41038,c_7071]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_1778,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_556,c_1590]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_2337,plain,
% 15.58/2.55      ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_2271,c_604]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_2363,plain,
% 15.58/2.55      ( k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 15.58/2.55      inference(light_normalisation,[status(thm)],[c_2337,c_1585]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_2364,plain,
% 15.58/2.55      ( k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_2363,c_604,c_1387]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_2993,plain,
% 15.58/2.55      ( k5_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_1,c_2364]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_41183,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_41182,c_1778,c_2993,c_7071]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_2311,plain,
% 15.58/2.55      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 15.58/2.55      inference(superposition,[status(thm)],[c_2271,c_1590]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_8982,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_7069,c_2311]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_41288,plain,
% 15.58/2.55      ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_41183,c_8982]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_16,negated_conjecture,
% 15.58/2.55      ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 15.58/2.55      inference(cnf_transformation,[],[f61]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_762,plain,
% 15.58/2.55      ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_604,c_16]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_47819,plain,
% 15.58/2.55      ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 15.58/2.55      inference(demodulation,[status(thm)],[c_41288,c_762]) ).
% 15.58/2.55  
% 15.58/2.55  cnf(c_47888,plain,
% 15.58/2.55      ( $false ),
% 15.58/2.55      inference(equality_resolution_simp,[status(thm)],[c_47819]) ).
% 15.58/2.55  
% 15.58/2.55  
% 15.58/2.55  % SZS output end CNFRefutation for theBenchmark.p
% 15.58/2.55  
% 15.58/2.55  ------                               Statistics
% 15.58/2.55  
% 15.58/2.55  ------ General
% 15.58/2.55  
% 15.58/2.55  abstr_ref_over_cycles:                  0
% 15.58/2.55  abstr_ref_under_cycles:                 0
% 15.58/2.55  gc_basic_clause_elim:                   0
% 15.58/2.55  forced_gc_time:                         0
% 15.58/2.55  parsing_time:                           0.007
% 15.58/2.55  unif_index_cands_time:                  0.
% 15.58/2.55  unif_index_add_time:                    0.
% 15.58/2.55  orderings_time:                         0.
% 15.58/2.55  out_proof_time:                         0.014
% 15.58/2.55  total_time:                             1.62
% 15.58/2.55  num_of_symbols:                         42
% 15.58/2.55  num_of_terms:                           68224
% 15.58/2.55  
% 15.58/2.55  ------ Preprocessing
% 15.58/2.55  
% 15.58/2.55  num_of_splits:                          0
% 15.58/2.55  num_of_split_atoms:                     0
% 15.58/2.55  num_of_reused_defs:                     0
% 15.58/2.55  num_eq_ax_congr_red:                    0
% 15.58/2.55  num_of_sem_filtered_clauses:            1
% 15.58/2.55  num_of_subtypes:                        0
% 15.58/2.55  monotx_restored_types:                  0
% 15.58/2.55  sat_num_of_epr_types:                   0
% 15.58/2.55  sat_num_of_non_cyclic_types:            0
% 15.58/2.55  sat_guarded_non_collapsed_types:        0
% 15.58/2.55  num_pure_diseq_elim:                    0
% 15.58/2.55  simp_replaced_by:                       0
% 15.58/2.55  res_preprocessed:                       74
% 15.58/2.55  prep_upred:                             0
% 15.58/2.55  prep_unflattend:                        0
% 15.58/2.55  smt_new_axioms:                         0
% 15.58/2.55  pred_elim_cands:                        2
% 15.58/2.55  pred_elim:                              0
% 15.58/2.55  pred_elim_cl:                           0
% 15.58/2.55  pred_elim_cycles:                       1
% 15.58/2.55  merged_defs:                            0
% 15.58/2.55  merged_defs_ncl:                        0
% 15.58/2.55  bin_hyper_res:                          0
% 15.58/2.55  prep_cycles:                            3
% 15.58/2.55  pred_elim_time:                         0.
% 15.58/2.55  splitting_time:                         0.
% 15.58/2.55  sem_filter_time:                        0.
% 15.58/2.55  monotx_time:                            0.
% 15.58/2.55  subtype_inf_time:                       0.
% 15.58/2.55  
% 15.58/2.55  ------ Problem properties
% 15.58/2.55  
% 15.58/2.55  clauses:                                17
% 15.58/2.55  conjectures:                            1
% 15.58/2.55  epr:                                    0
% 15.58/2.55  horn:                                   17
% 15.58/2.55  ground:                                 1
% 15.58/2.55  unary:                                  5
% 15.58/2.55  binary:                                 7
% 15.58/2.55  lits:                                   37
% 15.58/2.55  lits_eq:                                11
% 15.58/2.55  fd_pure:                                0
% 15.58/2.55  fd_pseudo:                              0
% 15.58/2.55  fd_cond:                                0
% 15.58/2.55  fd_pseudo_cond:                         0
% 15.58/2.55  ac_symbols:                             0
% 15.58/2.55  
% 15.58/2.55  ------ Propositional Solver
% 15.58/2.55  
% 15.58/2.55  prop_solver_calls:                      28
% 15.58/2.55  prop_fast_solver_calls:                 669
% 15.58/2.55  smt_solver_calls:                       0
% 15.58/2.55  smt_fast_solver_calls:                  0
% 15.58/2.55  prop_num_of_clauses:                    13035
% 15.58/2.55  prop_preprocess_simplified:             15547
% 15.58/2.55  prop_fo_subsumed:                       11
% 15.58/2.55  prop_solver_time:                       0.
% 15.58/2.55  smt_solver_time:                        0.
% 15.58/2.55  smt_fast_solver_time:                   0.
% 15.58/2.55  prop_fast_solver_time:                  0.
% 15.58/2.55  prop_unsat_core_time:                   0.
% 15.58/2.55  
% 15.58/2.55  ------ QBF
% 15.58/2.55  
% 15.58/2.55  qbf_q_res:                              0
% 15.58/2.55  qbf_num_tautologies:                    0
% 15.58/2.55  qbf_prep_cycles:                        0
% 15.58/2.55  
% 15.58/2.55  ------ BMC1
% 15.58/2.55  
% 15.58/2.55  bmc1_current_bound:                     -1
% 15.58/2.55  bmc1_last_solved_bound:                 -1
% 15.58/2.55  bmc1_unsat_core_size:                   -1
% 15.58/2.55  bmc1_unsat_core_parents_size:           -1
% 15.58/2.55  bmc1_merge_next_fun:                    0
% 15.58/2.55  bmc1_unsat_core_clauses_time:           0.
% 15.58/2.55  
% 15.58/2.55  ------ Instantiation
% 15.58/2.55  
% 15.58/2.55  inst_num_of_clauses:                    3206
% 15.58/2.55  inst_num_in_passive:                    1415
% 15.58/2.55  inst_num_in_active:                     1135
% 15.58/2.55  inst_num_in_unprocessed:                657
% 15.58/2.55  inst_num_of_loops:                      1180
% 15.58/2.55  inst_num_of_learning_restarts:          0
% 15.58/2.55  inst_num_moves_active_passive:          41
% 15.58/2.55  inst_lit_activity:                      0
% 15.58/2.55  inst_lit_activity_moves:                0
% 15.58/2.55  inst_num_tautologies:                   0
% 15.58/2.55  inst_num_prop_implied:                  0
% 15.58/2.55  inst_num_existing_simplified:           0
% 15.58/2.55  inst_num_eq_res_simplified:             0
% 15.58/2.55  inst_num_child_elim:                    0
% 15.58/2.55  inst_num_of_dismatching_blockings:      1100
% 15.58/2.55  inst_num_of_non_proper_insts:           3019
% 15.58/2.55  inst_num_of_duplicates:                 0
% 15.58/2.55  inst_inst_num_from_inst_to_res:         0
% 15.58/2.55  inst_dismatching_checking_time:         0.
% 15.58/2.55  
% 15.58/2.55  ------ Resolution
% 15.58/2.55  
% 15.58/2.55  res_num_of_clauses:                     0
% 15.58/2.55  res_num_in_passive:                     0
% 15.58/2.55  res_num_in_active:                      0
% 15.58/2.55  res_num_of_loops:                       77
% 15.58/2.55  res_forward_subset_subsumed:            561
% 15.58/2.55  res_backward_subset_subsumed:           6
% 15.58/2.55  res_forward_subsumed:                   0
% 15.58/2.55  res_backward_subsumed:                  0
% 15.58/2.55  res_forward_subsumption_resolution:     0
% 15.58/2.55  res_backward_subsumption_resolution:    0
% 15.58/2.55  res_clause_to_clause_subsumption:       40513
% 15.58/2.55  res_orphan_elimination:                 0
% 15.58/2.55  res_tautology_del:                      306
% 15.58/2.55  res_num_eq_res_simplified:              0
% 15.58/2.55  res_num_sel_changes:                    0
% 15.58/2.55  res_moves_from_active_to_pass:          0
% 15.58/2.55  
% 15.58/2.55  ------ Superposition
% 15.58/2.55  
% 15.58/2.55  sup_time_total:                         0.
% 15.58/2.55  sup_time_generating:                    0.
% 15.58/2.55  sup_time_sim_full:                      0.
% 15.58/2.55  sup_time_sim_immed:                     0.
% 15.58/2.55  
% 15.58/2.55  sup_num_of_clauses:                     4138
% 15.58/2.55  sup_num_in_active:                      169
% 15.58/2.55  sup_num_in_passive:                     3969
% 15.58/2.55  sup_num_of_loops:                       234
% 15.58/2.55  sup_fw_superposition:                   12656
% 15.58/2.55  sup_bw_superposition:                   13605
% 15.58/2.55  sup_immediate_simplified:               7967
% 15.58/2.55  sup_given_eliminated:                   0
% 15.58/2.55  comparisons_done:                       0
% 15.58/2.55  comparisons_avoided:                    0
% 15.58/2.55  
% 15.58/2.55  ------ Simplifications
% 15.58/2.55  
% 15.58/2.55  
% 15.58/2.55  sim_fw_subset_subsumed:                 49
% 15.58/2.55  sim_bw_subset_subsumed:                 47
% 15.58/2.55  sim_fw_subsumed:                        1575
% 15.58/2.55  sim_bw_subsumed:                        11
% 15.58/2.55  sim_fw_subsumption_res:                 0
% 15.58/2.55  sim_bw_subsumption_res:                 0
% 15.58/2.55  sim_tautology_del:                      3
% 15.58/2.55  sim_eq_tautology_del:                   1297
% 15.58/2.55  sim_eq_res_simp:                        0
% 15.58/2.55  sim_fw_demodulated:                     4966
% 15.58/2.55  sim_bw_demodulated:                     93
% 15.58/2.55  sim_light_normalised:                   2947
% 15.58/2.55  sim_joinable_taut:                      0
% 15.58/2.55  sim_joinable_simp:                      0
% 15.58/2.55  sim_ac_normalised:                      0
% 15.58/2.55  sim_smt_subsumption:                    0
% 15.58/2.55  
%------------------------------------------------------------------------------
