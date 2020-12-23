%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:56 EST 2020

% Result     : Theorem 7.42s
% Output     : CNFRefutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 268 expanded)
%              Number of clauses        :   46 ( 100 expanded)
%              Number of leaves         :   18 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  198 ( 441 expanded)
%              Number of equality atoms :  101 ( 224 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f72])).

fof(f74,plain,(
    ! [X0,X1] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f48,f73])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f22,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f22])).

fof(f40,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f23])).

fof(f42,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42])).

fof(f70,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f70,f74])).

cnf(c_20,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_655,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_656,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_921,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_655,c_656])).

cnf(c_17,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_657,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1095,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_657])).

cnf(c_1649,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1095,c_655])).

cnf(c_13,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_125,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_2,c_0])).

cnf(c_126,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_125])).

cnf(c_653,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_126])).

cnf(c_15077,plain,
    ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_653])).

cnf(c_15764,plain,
    ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15077,c_655])).

cnf(c_15770,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_15764])).

cnf(c_6,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_662,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2116,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_662])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_663,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1312,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_655,c_663])).

cnf(c_1313,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1312,c_921])).

cnf(c_2117,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2116,c_1313])).

cnf(c_7805,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2117,c_655])).

cnf(c_16016,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[status(thm)],[c_15770,c_7805])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_660,plain,
    ( k7_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_664,plain,
    ( k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2374,plain,
    ( k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_655,c_664])).

cnf(c_2381,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_2374,c_13])).

cnf(c_2382,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_2381,c_1313])).

cnf(c_3700,plain,
    ( k7_relat_1(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X0)))) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_660,c_2382])).

cnf(c_3706,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X0))))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_655,c_3700])).

cnf(c_14,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3721,plain,
    ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_3706,c_14])).

cnf(c_16018,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_16016,c_3721])).

cnf(c_21,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_924,plain,
    ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_921,c_21])).

cnf(c_2647,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_2382,c_924])).

cnf(c_16172,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_16018,c_2647])).

cnf(c_16217,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_16172])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:36:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.42/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.42/1.51  
% 7.42/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.42/1.51  
% 7.42/1.51  ------  iProver source info
% 7.42/1.51  
% 7.42/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.42/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.42/1.51  git: non_committed_changes: false
% 7.42/1.51  git: last_make_outside_of_git: false
% 7.42/1.51  
% 7.42/1.51  ------ 
% 7.42/1.51  
% 7.42/1.51  ------ Input Options
% 7.42/1.51  
% 7.42/1.51  --out_options                           all
% 7.42/1.51  --tptp_safe_out                         true
% 7.42/1.51  --problem_path                          ""
% 7.42/1.51  --include_path                          ""
% 7.42/1.51  --clausifier                            res/vclausify_rel
% 7.42/1.51  --clausifier_options                    --mode clausify
% 7.42/1.51  --stdin                                 false
% 7.42/1.51  --stats_out                             all
% 7.42/1.51  
% 7.42/1.51  ------ General Options
% 7.42/1.51  
% 7.42/1.51  --fof                                   false
% 7.42/1.51  --time_out_real                         305.
% 7.42/1.51  --time_out_virtual                      -1.
% 7.42/1.51  --symbol_type_check                     false
% 7.42/1.51  --clausify_out                          false
% 7.42/1.51  --sig_cnt_out                           false
% 7.42/1.51  --trig_cnt_out                          false
% 7.42/1.51  --trig_cnt_out_tolerance                1.
% 7.42/1.51  --trig_cnt_out_sk_spl                   false
% 7.42/1.51  --abstr_cl_out                          false
% 7.42/1.51  
% 7.42/1.51  ------ Global Options
% 7.42/1.51  
% 7.42/1.51  --schedule                              default
% 7.42/1.51  --add_important_lit                     false
% 7.42/1.51  --prop_solver_per_cl                    1000
% 7.42/1.51  --min_unsat_core                        false
% 7.42/1.51  --soft_assumptions                      false
% 7.42/1.51  --soft_lemma_size                       3
% 7.42/1.51  --prop_impl_unit_size                   0
% 7.42/1.51  --prop_impl_unit                        []
% 7.42/1.51  --share_sel_clauses                     true
% 7.42/1.51  --reset_solvers                         false
% 7.42/1.51  --bc_imp_inh                            [conj_cone]
% 7.42/1.51  --conj_cone_tolerance                   3.
% 7.42/1.51  --extra_neg_conj                        none
% 7.42/1.51  --large_theory_mode                     true
% 7.42/1.51  --prolific_symb_bound                   200
% 7.42/1.51  --lt_threshold                          2000
% 7.42/1.51  --clause_weak_htbl                      true
% 7.42/1.51  --gc_record_bc_elim                     false
% 7.42/1.51  
% 7.42/1.51  ------ Preprocessing Options
% 7.42/1.51  
% 7.42/1.51  --preprocessing_flag                    true
% 7.42/1.51  --time_out_prep_mult                    0.1
% 7.42/1.51  --splitting_mode                        input
% 7.42/1.51  --splitting_grd                         true
% 7.42/1.51  --splitting_cvd                         false
% 7.42/1.51  --splitting_cvd_svl                     false
% 7.42/1.51  --splitting_nvd                         32
% 7.42/1.51  --sub_typing                            true
% 7.42/1.51  --prep_gs_sim                           true
% 7.42/1.51  --prep_unflatten                        true
% 7.42/1.51  --prep_res_sim                          true
% 7.42/1.51  --prep_upred                            true
% 7.42/1.51  --prep_sem_filter                       exhaustive
% 7.42/1.51  --prep_sem_filter_out                   false
% 7.42/1.51  --pred_elim                             true
% 7.42/1.51  --res_sim_input                         true
% 7.42/1.51  --eq_ax_congr_red                       true
% 7.42/1.51  --pure_diseq_elim                       true
% 7.42/1.51  --brand_transform                       false
% 7.42/1.51  --non_eq_to_eq                          false
% 7.42/1.51  --prep_def_merge                        true
% 7.42/1.51  --prep_def_merge_prop_impl              false
% 7.42/1.51  --prep_def_merge_mbd                    true
% 7.42/1.51  --prep_def_merge_tr_red                 false
% 7.42/1.51  --prep_def_merge_tr_cl                  false
% 7.42/1.51  --smt_preprocessing                     true
% 7.42/1.51  --smt_ac_axioms                         fast
% 7.42/1.51  --preprocessed_out                      false
% 7.42/1.51  --preprocessed_stats                    false
% 7.42/1.51  
% 7.42/1.51  ------ Abstraction refinement Options
% 7.42/1.51  
% 7.42/1.51  --abstr_ref                             []
% 7.42/1.51  --abstr_ref_prep                        false
% 7.42/1.51  --abstr_ref_until_sat                   false
% 7.42/1.51  --abstr_ref_sig_restrict                funpre
% 7.42/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.42/1.51  --abstr_ref_under                       []
% 7.42/1.51  
% 7.42/1.51  ------ SAT Options
% 7.42/1.51  
% 7.42/1.51  --sat_mode                              false
% 7.42/1.51  --sat_fm_restart_options                ""
% 7.42/1.51  --sat_gr_def                            false
% 7.42/1.51  --sat_epr_types                         true
% 7.42/1.51  --sat_non_cyclic_types                  false
% 7.42/1.51  --sat_finite_models                     false
% 7.42/1.51  --sat_fm_lemmas                         false
% 7.42/1.51  --sat_fm_prep                           false
% 7.42/1.51  --sat_fm_uc_incr                        true
% 7.42/1.51  --sat_out_model                         small
% 7.42/1.51  --sat_out_clauses                       false
% 7.42/1.51  
% 7.42/1.51  ------ QBF Options
% 7.42/1.51  
% 7.42/1.51  --qbf_mode                              false
% 7.42/1.51  --qbf_elim_univ                         false
% 7.42/1.51  --qbf_dom_inst                          none
% 7.42/1.51  --qbf_dom_pre_inst                      false
% 7.42/1.51  --qbf_sk_in                             false
% 7.42/1.51  --qbf_pred_elim                         true
% 7.42/1.51  --qbf_split                             512
% 7.42/1.51  
% 7.42/1.51  ------ BMC1 Options
% 7.42/1.51  
% 7.42/1.51  --bmc1_incremental                      false
% 7.42/1.51  --bmc1_axioms                           reachable_all
% 7.42/1.51  --bmc1_min_bound                        0
% 7.42/1.51  --bmc1_max_bound                        -1
% 7.42/1.51  --bmc1_max_bound_default                -1
% 7.42/1.51  --bmc1_symbol_reachability              true
% 7.42/1.51  --bmc1_property_lemmas                  false
% 7.42/1.51  --bmc1_k_induction                      false
% 7.42/1.51  --bmc1_non_equiv_states                 false
% 7.42/1.51  --bmc1_deadlock                         false
% 7.42/1.51  --bmc1_ucm                              false
% 7.42/1.51  --bmc1_add_unsat_core                   none
% 7.42/1.51  --bmc1_unsat_core_children              false
% 7.42/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.42/1.51  --bmc1_out_stat                         full
% 7.42/1.51  --bmc1_ground_init                      false
% 7.42/1.51  --bmc1_pre_inst_next_state              false
% 7.42/1.51  --bmc1_pre_inst_state                   false
% 7.42/1.51  --bmc1_pre_inst_reach_state             false
% 7.42/1.51  --bmc1_out_unsat_core                   false
% 7.42/1.51  --bmc1_aig_witness_out                  false
% 7.42/1.51  --bmc1_verbose                          false
% 7.42/1.51  --bmc1_dump_clauses_tptp                false
% 7.42/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.42/1.51  --bmc1_dump_file                        -
% 7.42/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.42/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.42/1.51  --bmc1_ucm_extend_mode                  1
% 7.42/1.51  --bmc1_ucm_init_mode                    2
% 7.42/1.51  --bmc1_ucm_cone_mode                    none
% 7.42/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.42/1.51  --bmc1_ucm_relax_model                  4
% 7.42/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.42/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.42/1.51  --bmc1_ucm_layered_model                none
% 7.42/1.51  --bmc1_ucm_max_lemma_size               10
% 7.42/1.51  
% 7.42/1.51  ------ AIG Options
% 7.42/1.51  
% 7.42/1.51  --aig_mode                              false
% 7.42/1.51  
% 7.42/1.51  ------ Instantiation Options
% 7.42/1.51  
% 7.42/1.51  --instantiation_flag                    true
% 7.42/1.51  --inst_sos_flag                         false
% 7.42/1.51  --inst_sos_phase                        true
% 7.42/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.42/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.42/1.51  --inst_lit_sel_side                     num_symb
% 7.42/1.51  --inst_solver_per_active                1400
% 7.42/1.51  --inst_solver_calls_frac                1.
% 7.42/1.51  --inst_passive_queue_type               priority_queues
% 7.42/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.42/1.51  --inst_passive_queues_freq              [25;2]
% 7.42/1.51  --inst_dismatching                      true
% 7.42/1.51  --inst_eager_unprocessed_to_passive     true
% 7.42/1.51  --inst_prop_sim_given                   true
% 7.42/1.51  --inst_prop_sim_new                     false
% 7.42/1.51  --inst_subs_new                         false
% 7.42/1.51  --inst_eq_res_simp                      false
% 7.42/1.51  --inst_subs_given                       false
% 7.42/1.51  --inst_orphan_elimination               true
% 7.42/1.51  --inst_learning_loop_flag               true
% 7.42/1.51  --inst_learning_start                   3000
% 7.42/1.51  --inst_learning_factor                  2
% 7.42/1.51  --inst_start_prop_sim_after_learn       3
% 7.42/1.51  --inst_sel_renew                        solver
% 7.42/1.51  --inst_lit_activity_flag                true
% 7.42/1.51  --inst_restr_to_given                   false
% 7.42/1.51  --inst_activity_threshold               500
% 7.42/1.51  --inst_out_proof                        true
% 7.42/1.51  
% 7.42/1.51  ------ Resolution Options
% 7.42/1.51  
% 7.42/1.51  --resolution_flag                       true
% 7.42/1.51  --res_lit_sel                           adaptive
% 7.42/1.51  --res_lit_sel_side                      none
% 7.42/1.51  --res_ordering                          kbo
% 7.42/1.51  --res_to_prop_solver                    active
% 7.42/1.51  --res_prop_simpl_new                    false
% 7.42/1.51  --res_prop_simpl_given                  true
% 7.42/1.51  --res_passive_queue_type                priority_queues
% 7.42/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.42/1.51  --res_passive_queues_freq               [15;5]
% 7.42/1.51  --res_forward_subs                      full
% 7.42/1.51  --res_backward_subs                     full
% 7.42/1.51  --res_forward_subs_resolution           true
% 7.42/1.51  --res_backward_subs_resolution          true
% 7.42/1.51  --res_orphan_elimination                true
% 7.42/1.51  --res_time_limit                        2.
% 7.42/1.51  --res_out_proof                         true
% 7.42/1.51  
% 7.42/1.51  ------ Superposition Options
% 7.42/1.51  
% 7.42/1.51  --superposition_flag                    true
% 7.42/1.51  --sup_passive_queue_type                priority_queues
% 7.42/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.42/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.42/1.51  --demod_completeness_check              fast
% 7.42/1.51  --demod_use_ground                      true
% 7.42/1.51  --sup_to_prop_solver                    passive
% 7.42/1.51  --sup_prop_simpl_new                    true
% 7.42/1.51  --sup_prop_simpl_given                  true
% 7.42/1.51  --sup_fun_splitting                     false
% 7.42/1.51  --sup_smt_interval                      50000
% 7.42/1.51  
% 7.42/1.51  ------ Superposition Simplification Setup
% 7.42/1.51  
% 7.42/1.51  --sup_indices_passive                   []
% 7.42/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.42/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.51  --sup_full_bw                           [BwDemod]
% 7.42/1.51  --sup_immed_triv                        [TrivRules]
% 7.42/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.42/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.51  --sup_immed_bw_main                     []
% 7.42/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.42/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.51  
% 7.42/1.51  ------ Combination Options
% 7.42/1.51  
% 7.42/1.51  --comb_res_mult                         3
% 7.42/1.51  --comb_sup_mult                         2
% 7.42/1.51  --comb_inst_mult                        10
% 7.42/1.51  
% 7.42/1.51  ------ Debug Options
% 7.42/1.51  
% 7.42/1.51  --dbg_backtrace                         false
% 7.42/1.51  --dbg_dump_prop_clauses                 false
% 7.42/1.51  --dbg_dump_prop_clauses_file            -
% 7.42/1.51  --dbg_out_stat                          false
% 7.42/1.51  ------ Parsing...
% 7.42/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.42/1.51  
% 7.42/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.42/1.51  
% 7.42/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.42/1.51  
% 7.42/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.42/1.51  ------ Proving...
% 7.42/1.51  ------ Problem Properties 
% 7.42/1.51  
% 7.42/1.51  
% 7.42/1.51  clauses                                 19
% 7.42/1.51  conjectures                             1
% 7.42/1.51  EPR                                     1
% 7.42/1.51  Horn                                    19
% 7.42/1.51  unary                                   6
% 7.42/1.51  binary                                  7
% 7.42/1.51  lits                                    38
% 7.42/1.51  lits eq                                 13
% 7.42/1.51  fd_pure                                 0
% 7.42/1.51  fd_pseudo                               0
% 7.42/1.51  fd_cond                                 0
% 7.42/1.51  fd_pseudo_cond                          0
% 7.42/1.51  AC symbols                              0
% 7.42/1.51  
% 7.42/1.51  ------ Schedule dynamic 5 is on 
% 7.42/1.51  
% 7.42/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.42/1.51  
% 7.42/1.51  
% 7.42/1.51  ------ 
% 7.42/1.51  Current options:
% 7.42/1.51  ------ 
% 7.42/1.51  
% 7.42/1.51  ------ Input Options
% 7.42/1.51  
% 7.42/1.51  --out_options                           all
% 7.42/1.51  --tptp_safe_out                         true
% 7.42/1.51  --problem_path                          ""
% 7.42/1.51  --include_path                          ""
% 7.42/1.51  --clausifier                            res/vclausify_rel
% 7.42/1.51  --clausifier_options                    --mode clausify
% 7.42/1.51  --stdin                                 false
% 7.42/1.51  --stats_out                             all
% 7.42/1.51  
% 7.42/1.51  ------ General Options
% 7.42/1.51  
% 7.42/1.51  --fof                                   false
% 7.42/1.51  --time_out_real                         305.
% 7.42/1.51  --time_out_virtual                      -1.
% 7.42/1.51  --symbol_type_check                     false
% 7.42/1.51  --clausify_out                          false
% 7.42/1.51  --sig_cnt_out                           false
% 7.42/1.51  --trig_cnt_out                          false
% 7.42/1.51  --trig_cnt_out_tolerance                1.
% 7.42/1.51  --trig_cnt_out_sk_spl                   false
% 7.42/1.51  --abstr_cl_out                          false
% 7.42/1.51  
% 7.42/1.51  ------ Global Options
% 7.42/1.51  
% 7.42/1.51  --schedule                              default
% 7.42/1.51  --add_important_lit                     false
% 7.42/1.51  --prop_solver_per_cl                    1000
% 7.42/1.51  --min_unsat_core                        false
% 7.42/1.51  --soft_assumptions                      false
% 7.42/1.51  --soft_lemma_size                       3
% 7.42/1.51  --prop_impl_unit_size                   0
% 7.42/1.51  --prop_impl_unit                        []
% 7.42/1.51  --share_sel_clauses                     true
% 7.42/1.51  --reset_solvers                         false
% 7.42/1.51  --bc_imp_inh                            [conj_cone]
% 7.42/1.51  --conj_cone_tolerance                   3.
% 7.42/1.51  --extra_neg_conj                        none
% 7.42/1.51  --large_theory_mode                     true
% 7.42/1.51  --prolific_symb_bound                   200
% 7.42/1.51  --lt_threshold                          2000
% 7.42/1.51  --clause_weak_htbl                      true
% 7.42/1.51  --gc_record_bc_elim                     false
% 7.42/1.51  
% 7.42/1.51  ------ Preprocessing Options
% 7.42/1.51  
% 7.42/1.51  --preprocessing_flag                    true
% 7.42/1.51  --time_out_prep_mult                    0.1
% 7.42/1.51  --splitting_mode                        input
% 7.42/1.51  --splitting_grd                         true
% 7.42/1.51  --splitting_cvd                         false
% 7.42/1.51  --splitting_cvd_svl                     false
% 7.42/1.51  --splitting_nvd                         32
% 7.42/1.51  --sub_typing                            true
% 7.42/1.51  --prep_gs_sim                           true
% 7.42/1.51  --prep_unflatten                        true
% 7.42/1.51  --prep_res_sim                          true
% 7.42/1.51  --prep_upred                            true
% 7.42/1.51  --prep_sem_filter                       exhaustive
% 7.42/1.51  --prep_sem_filter_out                   false
% 7.42/1.51  --pred_elim                             true
% 7.42/1.51  --res_sim_input                         true
% 7.42/1.51  --eq_ax_congr_red                       true
% 7.42/1.51  --pure_diseq_elim                       true
% 7.42/1.51  --brand_transform                       false
% 7.42/1.51  --non_eq_to_eq                          false
% 7.42/1.51  --prep_def_merge                        true
% 7.42/1.51  --prep_def_merge_prop_impl              false
% 7.42/1.51  --prep_def_merge_mbd                    true
% 7.42/1.51  --prep_def_merge_tr_red                 false
% 7.42/1.51  --prep_def_merge_tr_cl                  false
% 7.42/1.51  --smt_preprocessing                     true
% 7.42/1.51  --smt_ac_axioms                         fast
% 7.42/1.51  --preprocessed_out                      false
% 7.42/1.51  --preprocessed_stats                    false
% 7.42/1.51  
% 7.42/1.51  ------ Abstraction refinement Options
% 7.42/1.51  
% 7.42/1.51  --abstr_ref                             []
% 7.42/1.51  --abstr_ref_prep                        false
% 7.42/1.51  --abstr_ref_until_sat                   false
% 7.42/1.51  --abstr_ref_sig_restrict                funpre
% 7.42/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.42/1.51  --abstr_ref_under                       []
% 7.42/1.51  
% 7.42/1.51  ------ SAT Options
% 7.42/1.51  
% 7.42/1.51  --sat_mode                              false
% 7.42/1.51  --sat_fm_restart_options                ""
% 7.42/1.51  --sat_gr_def                            false
% 7.42/1.51  --sat_epr_types                         true
% 7.42/1.51  --sat_non_cyclic_types                  false
% 7.42/1.51  --sat_finite_models                     false
% 7.42/1.51  --sat_fm_lemmas                         false
% 7.42/1.51  --sat_fm_prep                           false
% 7.42/1.51  --sat_fm_uc_incr                        true
% 7.42/1.51  --sat_out_model                         small
% 7.42/1.51  --sat_out_clauses                       false
% 7.42/1.51  
% 7.42/1.51  ------ QBF Options
% 7.42/1.51  
% 7.42/1.51  --qbf_mode                              false
% 7.42/1.51  --qbf_elim_univ                         false
% 7.42/1.51  --qbf_dom_inst                          none
% 7.42/1.51  --qbf_dom_pre_inst                      false
% 7.42/1.51  --qbf_sk_in                             false
% 7.42/1.51  --qbf_pred_elim                         true
% 7.42/1.51  --qbf_split                             512
% 7.42/1.51  
% 7.42/1.51  ------ BMC1 Options
% 7.42/1.51  
% 7.42/1.51  --bmc1_incremental                      false
% 7.42/1.51  --bmc1_axioms                           reachable_all
% 7.42/1.51  --bmc1_min_bound                        0
% 7.42/1.51  --bmc1_max_bound                        -1
% 7.42/1.51  --bmc1_max_bound_default                -1
% 7.42/1.51  --bmc1_symbol_reachability              true
% 7.42/1.51  --bmc1_property_lemmas                  false
% 7.42/1.51  --bmc1_k_induction                      false
% 7.42/1.51  --bmc1_non_equiv_states                 false
% 7.42/1.51  --bmc1_deadlock                         false
% 7.42/1.51  --bmc1_ucm                              false
% 7.42/1.51  --bmc1_add_unsat_core                   none
% 7.42/1.51  --bmc1_unsat_core_children              false
% 7.42/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.42/1.51  --bmc1_out_stat                         full
% 7.42/1.51  --bmc1_ground_init                      false
% 7.42/1.51  --bmc1_pre_inst_next_state              false
% 7.42/1.51  --bmc1_pre_inst_state                   false
% 7.42/1.51  --bmc1_pre_inst_reach_state             false
% 7.42/1.51  --bmc1_out_unsat_core                   false
% 7.42/1.51  --bmc1_aig_witness_out                  false
% 7.42/1.51  --bmc1_verbose                          false
% 7.42/1.51  --bmc1_dump_clauses_tptp                false
% 7.42/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.42/1.51  --bmc1_dump_file                        -
% 7.42/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.42/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.42/1.51  --bmc1_ucm_extend_mode                  1
% 7.42/1.51  --bmc1_ucm_init_mode                    2
% 7.42/1.51  --bmc1_ucm_cone_mode                    none
% 7.42/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.42/1.51  --bmc1_ucm_relax_model                  4
% 7.42/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.42/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.42/1.51  --bmc1_ucm_layered_model                none
% 7.42/1.51  --bmc1_ucm_max_lemma_size               10
% 7.42/1.51  
% 7.42/1.51  ------ AIG Options
% 7.42/1.51  
% 7.42/1.51  --aig_mode                              false
% 7.42/1.51  
% 7.42/1.51  ------ Instantiation Options
% 7.42/1.51  
% 7.42/1.51  --instantiation_flag                    true
% 7.42/1.51  --inst_sos_flag                         false
% 7.42/1.51  --inst_sos_phase                        true
% 7.42/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.42/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.42/1.51  --inst_lit_sel_side                     none
% 7.42/1.51  --inst_solver_per_active                1400
% 7.42/1.51  --inst_solver_calls_frac                1.
% 7.42/1.51  --inst_passive_queue_type               priority_queues
% 7.42/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.42/1.51  --inst_passive_queues_freq              [25;2]
% 7.42/1.51  --inst_dismatching                      true
% 7.42/1.51  --inst_eager_unprocessed_to_passive     true
% 7.42/1.51  --inst_prop_sim_given                   true
% 7.42/1.51  --inst_prop_sim_new                     false
% 7.42/1.51  --inst_subs_new                         false
% 7.42/1.51  --inst_eq_res_simp                      false
% 7.42/1.51  --inst_subs_given                       false
% 7.42/1.51  --inst_orphan_elimination               true
% 7.42/1.51  --inst_learning_loop_flag               true
% 7.42/1.51  --inst_learning_start                   3000
% 7.42/1.51  --inst_learning_factor                  2
% 7.42/1.51  --inst_start_prop_sim_after_learn       3
% 7.42/1.51  --inst_sel_renew                        solver
% 7.42/1.51  --inst_lit_activity_flag                true
% 7.42/1.51  --inst_restr_to_given                   false
% 7.42/1.51  --inst_activity_threshold               500
% 7.42/1.51  --inst_out_proof                        true
% 7.42/1.51  
% 7.42/1.51  ------ Resolution Options
% 7.42/1.51  
% 7.42/1.51  --resolution_flag                       false
% 7.42/1.51  --res_lit_sel                           adaptive
% 7.42/1.51  --res_lit_sel_side                      none
% 7.42/1.51  --res_ordering                          kbo
% 7.42/1.51  --res_to_prop_solver                    active
% 7.42/1.51  --res_prop_simpl_new                    false
% 7.42/1.51  --res_prop_simpl_given                  true
% 7.42/1.51  --res_passive_queue_type                priority_queues
% 7.42/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.42/1.51  --res_passive_queues_freq               [15;5]
% 7.42/1.51  --res_forward_subs                      full
% 7.42/1.51  --res_backward_subs                     full
% 7.42/1.51  --res_forward_subs_resolution           true
% 7.42/1.51  --res_backward_subs_resolution          true
% 7.42/1.51  --res_orphan_elimination                true
% 7.42/1.51  --res_time_limit                        2.
% 7.42/1.51  --res_out_proof                         true
% 7.42/1.51  
% 7.42/1.51  ------ Superposition Options
% 7.42/1.51  
% 7.42/1.51  --superposition_flag                    true
% 7.42/1.51  --sup_passive_queue_type                priority_queues
% 7.42/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.42/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.42/1.51  --demod_completeness_check              fast
% 7.42/1.51  --demod_use_ground                      true
% 7.42/1.51  --sup_to_prop_solver                    passive
% 7.42/1.51  --sup_prop_simpl_new                    true
% 7.42/1.51  --sup_prop_simpl_given                  true
% 7.42/1.51  --sup_fun_splitting                     false
% 7.42/1.51  --sup_smt_interval                      50000
% 7.42/1.51  
% 7.42/1.51  ------ Superposition Simplification Setup
% 7.42/1.51  
% 7.42/1.51  --sup_indices_passive                   []
% 7.42/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.42/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.42/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.51  --sup_full_bw                           [BwDemod]
% 7.42/1.51  --sup_immed_triv                        [TrivRules]
% 7.42/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.42/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.51  --sup_immed_bw_main                     []
% 7.42/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.42/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.42/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.42/1.51  
% 7.42/1.51  ------ Combination Options
% 7.42/1.51  
% 7.42/1.51  --comb_res_mult                         3
% 7.42/1.51  --comb_sup_mult                         2
% 7.42/1.51  --comb_inst_mult                        10
% 7.42/1.51  
% 7.42/1.51  ------ Debug Options
% 7.42/1.51  
% 7.42/1.51  --dbg_backtrace                         false
% 7.42/1.51  --dbg_dump_prop_clauses                 false
% 7.42/1.51  --dbg_dump_prop_clauses_file            -
% 7.42/1.51  --dbg_out_stat                          false
% 7.42/1.51  
% 7.42/1.51  
% 7.42/1.51  
% 7.42/1.51  
% 7.42/1.51  ------ Proving...
% 7.42/1.51  
% 7.42/1.51  
% 7.42/1.51  % SZS status Theorem for theBenchmark.p
% 7.42/1.51  
% 7.42/1.51   Resolution empty clause
% 7.42/1.51  
% 7.42/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.42/1.51  
% 7.42/1.51  fof(f21,axiom,(
% 7.42/1.51    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 7.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.51  
% 7.42/1.51  fof(f24,plain,(
% 7.42/1.51    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 7.42/1.51    inference(pure_predicate_removal,[],[f21])).
% 7.42/1.51  
% 7.42/1.51  fof(f68,plain,(
% 7.42/1.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.42/1.51    inference(cnf_transformation,[],[f24])).
% 7.42/1.51  
% 7.42/1.51  fof(f20,axiom,(
% 7.42/1.51    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 7.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.51  
% 7.42/1.51  fof(f39,plain,(
% 7.42/1.51    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.42/1.51    inference(ennf_transformation,[],[f20])).
% 7.42/1.51  
% 7.42/1.51  fof(f67,plain,(
% 7.42/1.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.42/1.51    inference(cnf_transformation,[],[f39])).
% 7.42/1.51  
% 7.42/1.51  fof(f19,axiom,(
% 7.42/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f38,plain,(
% 7.42/1.52    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 7.42/1.52    inference(ennf_transformation,[],[f19])).
% 7.42/1.52  
% 7.42/1.52  fof(f65,plain,(
% 7.42/1.52    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f38])).
% 7.42/1.52  
% 7.42/1.52  fof(f17,axiom,(
% 7.42/1.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f63,plain,(
% 7.42/1.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.42/1.52    inference(cnf_transformation,[],[f17])).
% 7.42/1.52  
% 7.42/1.52  fof(f15,axiom,(
% 7.42/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f35,plain,(
% 7.42/1.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.42/1.52    inference(ennf_transformation,[],[f15])).
% 7.42/1.52  
% 7.42/1.52  fof(f36,plain,(
% 7.42/1.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.42/1.52    inference(flattening,[],[f35])).
% 7.42/1.52  
% 7.42/1.52  fof(f60,plain,(
% 7.42/1.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f36])).
% 7.42/1.52  
% 7.42/1.52  fof(f7,axiom,(
% 7.42/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f25,plain,(
% 7.42/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.42/1.52    inference(ennf_transformation,[],[f7])).
% 7.42/1.52  
% 7.42/1.52  fof(f51,plain,(
% 7.42/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f25])).
% 7.42/1.52  
% 7.42/1.52  fof(f6,axiom,(
% 7.42/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f41,plain,(
% 7.42/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.42/1.52    inference(nnf_transformation,[],[f6])).
% 7.42/1.52  
% 7.42/1.52  fof(f50,plain,(
% 7.42/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f41])).
% 7.42/1.52  
% 7.42/1.52  fof(f11,axiom,(
% 7.42/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f29,plain,(
% 7.42/1.52    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.42/1.52    inference(ennf_transformation,[],[f11])).
% 7.42/1.52  
% 7.42/1.52  fof(f30,plain,(
% 7.42/1.52    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.42/1.52    inference(flattening,[],[f29])).
% 7.42/1.52  
% 7.42/1.52  fof(f55,plain,(
% 7.42/1.52    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f30])).
% 7.42/1.52  
% 7.42/1.52  fof(f10,axiom,(
% 7.42/1.52    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f28,plain,(
% 7.42/1.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 7.42/1.52    inference(ennf_transformation,[],[f10])).
% 7.42/1.52  
% 7.42/1.52  fof(f54,plain,(
% 7.42/1.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f28])).
% 7.42/1.52  
% 7.42/1.52  fof(f13,axiom,(
% 7.42/1.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f32,plain,(
% 7.42/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.42/1.52    inference(ennf_transformation,[],[f13])).
% 7.42/1.52  
% 7.42/1.52  fof(f57,plain,(
% 7.42/1.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f32])).
% 7.42/1.52  
% 7.42/1.52  fof(f5,axiom,(
% 7.42/1.52    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f48,plain,(
% 7.42/1.52    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f5])).
% 7.42/1.52  
% 7.42/1.52  fof(f1,axiom,(
% 7.42/1.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f44,plain,(
% 7.42/1.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f1])).
% 7.42/1.52  
% 7.42/1.52  fof(f2,axiom,(
% 7.42/1.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f45,plain,(
% 7.42/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f2])).
% 7.42/1.52  
% 7.42/1.52  fof(f3,axiom,(
% 7.42/1.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f46,plain,(
% 7.42/1.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f3])).
% 7.42/1.52  
% 7.42/1.52  fof(f4,axiom,(
% 7.42/1.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f47,plain,(
% 7.42/1.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f4])).
% 7.42/1.52  
% 7.42/1.52  fof(f71,plain,(
% 7.42/1.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.42/1.52    inference(definition_unfolding,[],[f46,f47])).
% 7.42/1.52  
% 7.42/1.52  fof(f72,plain,(
% 7.42/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 7.42/1.52    inference(definition_unfolding,[],[f45,f71])).
% 7.42/1.52  
% 7.42/1.52  fof(f73,plain,(
% 7.42/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 7.42/1.52    inference(definition_unfolding,[],[f44,f72])).
% 7.42/1.52  
% 7.42/1.52  fof(f74,plain,(
% 7.42/1.52    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.42/1.52    inference(definition_unfolding,[],[f48,f73])).
% 7.42/1.52  
% 7.42/1.52  fof(f76,plain,(
% 7.42/1.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 7.42/1.52    inference(definition_unfolding,[],[f57,f74])).
% 7.42/1.52  
% 7.42/1.52  fof(f9,axiom,(
% 7.42/1.52    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)))),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f27,plain,(
% 7.42/1.52    ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 7.42/1.52    inference(ennf_transformation,[],[f9])).
% 7.42/1.52  
% 7.42/1.52  fof(f53,plain,(
% 7.42/1.52    ( ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 7.42/1.52    inference(cnf_transformation,[],[f27])).
% 7.42/1.52  
% 7.42/1.52  fof(f75,plain,(
% 7.42/1.52    ( ! [X0,X1] : (k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 7.42/1.52    inference(definition_unfolding,[],[f53,f74])).
% 7.42/1.52  
% 7.42/1.52  fof(f62,plain,(
% 7.42/1.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.42/1.52    inference(cnf_transformation,[],[f17])).
% 7.42/1.52  
% 7.42/1.52  fof(f22,conjecture,(
% 7.42/1.52    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.42/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.42/1.52  
% 7.42/1.52  fof(f23,negated_conjecture,(
% 7.42/1.52    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.42/1.52    inference(negated_conjecture,[],[f22])).
% 7.42/1.52  
% 7.42/1.52  fof(f40,plain,(
% 7.42/1.52    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 7.42/1.52    inference(ennf_transformation,[],[f23])).
% 7.42/1.52  
% 7.42/1.52  fof(f42,plain,(
% 7.42/1.52    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.42/1.52    introduced(choice_axiom,[])).
% 7.42/1.52  
% 7.42/1.52  fof(f43,plain,(
% 7.42/1.52    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.42/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42])).
% 7.42/1.52  
% 7.42/1.52  fof(f70,plain,(
% 7.42/1.52    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.42/1.52    inference(cnf_transformation,[],[f43])).
% 7.42/1.52  
% 7.42/1.52  fof(f77,plain,(
% 7.42/1.52    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 7.42/1.52    inference(definition_unfolding,[],[f70,f74])).
% 7.42/1.52  
% 7.42/1.52  cnf(c_20,plain,
% 7.42/1.52      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.42/1.52      inference(cnf_transformation,[],[f68]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_655,plain,
% 7.42/1.52      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.42/1.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_18,plain,
% 7.42/1.52      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.42/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_656,plain,
% 7.42/1.52      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.42/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.42/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_921,plain,
% 7.42/1.52      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.42/1.52      inference(superposition,[status(thm)],[c_655,c_656]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_17,plain,
% 7.42/1.52      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 7.42/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_657,plain,
% 7.42/1.52      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
% 7.42/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.42/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_1095,plain,
% 7.42/1.52      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
% 7.42/1.52      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.42/1.52      inference(superposition,[status(thm)],[c_921,c_657]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_1649,plain,
% 7.42/1.52      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
% 7.42/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_1095,c_655]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_13,plain,
% 7.42/1.52      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.42/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_10,plain,
% 7.42/1.52      ( ~ r1_tarski(X0,X1)
% 7.42/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.42/1.52      | ~ v1_relat_1(X0)
% 7.42/1.52      | ~ v1_relat_1(X1) ),
% 7.42/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_2,plain,
% 7.42/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.42/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_0,plain,
% 7.42/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.42/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_125,plain,
% 7.42/1.52      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.42/1.52      | ~ r1_tarski(X0,X1)
% 7.42/1.52      | ~ v1_relat_1(X1) ),
% 7.42/1.52      inference(global_propositional_subsumption,[status(thm)],[c_10,c_2,c_0]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_126,plain,
% 7.42/1.52      ( ~ r1_tarski(X0,X1)
% 7.42/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.42/1.52      | ~ v1_relat_1(X1) ),
% 7.42/1.52      inference(renaming,[status(thm)],[c_125]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_653,plain,
% 7.42/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.42/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 7.42/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.42/1.52      inference(predicate_to_equality,[status(thm)],[c_126]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_15077,plain,
% 7.42/1.52      ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
% 7.42/1.52      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 7.42/1.52      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.42/1.52      inference(superposition,[status(thm)],[c_13,c_653]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_15764,plain,
% 7.42/1.52      ( r1_tarski(X0,k6_relat_1(X1)) != iProver_top
% 7.42/1.52      | r1_tarski(k2_relat_1(X0),X1) = iProver_top ),
% 7.42/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_15077,c_655]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_15770,plain,
% 7.42/1.52      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) = iProver_top ),
% 7.42/1.52      inference(superposition,[status(thm)],[c_1649,c_15764]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_6,plain,
% 7.42/1.52      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.42/1.52      | ~ v1_relat_1(X0)
% 7.42/1.52      | k8_relat_1(X1,X0) = X0 ),
% 7.42/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_662,plain,
% 7.42/1.52      ( k8_relat_1(X0,X1) = X1
% 7.42/1.52      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 7.42/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.42/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_2116,plain,
% 7.42/1.52      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 7.42/1.52      | r1_tarski(X1,X0) != iProver_top
% 7.42/1.52      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.42/1.52      inference(superposition,[status(thm)],[c_13,c_662]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_5,plain,
% 7.42/1.52      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 7.42/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_663,plain,
% 7.42/1.52      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 7.42/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.42/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_1312,plain,
% 7.42/1.52      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 7.42/1.52      inference(superposition,[status(thm)],[c_655,c_663]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_1313,plain,
% 7.42/1.52      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.42/1.52      inference(light_normalisation,[status(thm)],[c_1312,c_921]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_2117,plain,
% 7.42/1.52      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 7.42/1.52      | r1_tarski(X1,X0) != iProver_top
% 7.42/1.52      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.42/1.52      inference(demodulation,[status(thm)],[c_2116,c_1313]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_7805,plain,
% 7.42/1.52      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 7.42/1.52      | r1_tarski(X1,X0) != iProver_top ),
% 7.42/1.52      inference(forward_subsumption_resolution,[status(thm)],[c_2117,c_655]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_16016,plain,
% 7.42/1.52      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.42/1.52      inference(superposition,[status(thm)],[c_15770,c_7805]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_8,plain,
% 7.42/1.52      ( ~ v1_relat_1(X0)
% 7.42/1.52      | k7_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
% 7.42/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_660,plain,
% 7.42/1.52      ( k7_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
% 7.42/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.42/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_4,plain,
% 7.42/1.52      ( ~ v1_relat_1(X0)
% 7.42/1.52      | k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
% 7.42/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_664,plain,
% 7.42/1.52      ( k1_setfam_1(k4_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
% 7.42/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.42/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_2374,plain,
% 7.42/1.52      ( k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),k2_relat_1(k6_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 7.42/1.52      inference(superposition,[status(thm)],[c_655,c_664]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_2381,plain,
% 7.42/1.52      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 7.42/1.52      inference(light_normalisation,[status(thm)],[c_2374,c_13]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_2382,plain,
% 7.42/1.52      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 7.42/1.52      inference(demodulation,[status(thm)],[c_2381,c_1313]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_3700,plain,
% 7.42/1.52      ( k7_relat_1(X0,k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(X0)))) = k7_relat_1(X0,X1)
% 7.42/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.42/1.52      inference(demodulation,[status(thm)],[c_660,c_2382]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_3706,plain,
% 7.42/1.52      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X0))))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.42/1.52      inference(superposition,[status(thm)],[c_655,c_3700]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_14,plain,
% 7.42/1.52      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.42/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_3721,plain,
% 7.42/1.52      ( k7_relat_1(k6_relat_1(X0),k2_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.42/1.52      inference(light_normalisation,[status(thm)],[c_3706,c_14]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_16018,plain,
% 7.42/1.52      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.42/1.52      inference(light_normalisation,[status(thm)],[c_16016,c_3721]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_21,negated_conjecture,
% 7.42/1.52      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
% 7.42/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_924,plain,
% 7.42/1.52      ( k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.42/1.52      inference(demodulation,[status(thm)],[c_921,c_21]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_2647,plain,
% 7.42/1.52      ( k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.42/1.52      inference(demodulation,[status(thm)],[c_2382,c_924]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_16172,plain,
% 7.42/1.52      ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.42/1.52      inference(demodulation,[status(thm)],[c_16018,c_2647]) ).
% 7.42/1.52  
% 7.42/1.52  cnf(c_16217,plain,
% 7.42/1.52      ( $false ),
% 7.42/1.52      inference(equality_resolution_simp,[status(thm)],[c_16172]) ).
% 7.42/1.52  
% 7.42/1.52  
% 7.42/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.42/1.52  
% 7.42/1.52  ------                               Statistics
% 7.42/1.52  
% 7.42/1.52  ------ General
% 7.42/1.52  
% 7.42/1.52  abstr_ref_over_cycles:                  0
% 7.42/1.52  abstr_ref_under_cycles:                 0
% 7.42/1.52  gc_basic_clause_elim:                   0
% 7.42/1.52  forced_gc_time:                         0
% 7.42/1.52  parsing_time:                           0.01
% 7.42/1.52  unif_index_cands_time:                  0.
% 7.42/1.52  unif_index_add_time:                    0.
% 7.42/1.52  orderings_time:                         0.
% 7.42/1.52  out_proof_time:                         0.015
% 7.42/1.52  total_time:                             0.609
% 7.42/1.52  num_of_symbols:                         47
% 7.42/1.52  num_of_terms:                           21369
% 7.42/1.52  
% 7.42/1.52  ------ Preprocessing
% 7.42/1.52  
% 7.42/1.52  num_of_splits:                          0
% 7.42/1.52  num_of_split_atoms:                     0
% 7.42/1.52  num_of_reused_defs:                     0
% 7.42/1.52  num_eq_ax_congr_red:                    6
% 7.42/1.52  num_of_sem_filtered_clauses:            1
% 7.42/1.52  num_of_subtypes:                        0
% 7.42/1.52  monotx_restored_types:                  0
% 7.42/1.52  sat_num_of_epr_types:                   0
% 7.42/1.52  sat_num_of_non_cyclic_types:            0
% 7.42/1.52  sat_guarded_non_collapsed_types:        0
% 7.42/1.52  num_pure_diseq_elim:                    0
% 7.42/1.52  simp_replaced_by:                       0
% 7.42/1.52  res_preprocessed:                       106
% 7.42/1.52  prep_upred:                             0
% 7.42/1.52  prep_unflattend:                        2
% 7.42/1.52  smt_new_axioms:                         0
% 7.42/1.52  pred_elim_cands:                        2
% 7.42/1.52  pred_elim:                              2
% 7.42/1.52  pred_elim_cl:                           3
% 7.42/1.52  pred_elim_cycles:                       4
% 7.42/1.52  merged_defs:                            2
% 7.42/1.52  merged_defs_ncl:                        0
% 7.42/1.52  bin_hyper_res:                          3
% 7.42/1.52  prep_cycles:                            4
% 7.42/1.52  pred_elim_time:                         0.001
% 7.42/1.52  splitting_time:                         0.
% 7.42/1.52  sem_filter_time:                        0.
% 7.42/1.52  monotx_time:                            0.
% 7.42/1.52  subtype_inf_time:                       0.
% 7.42/1.52  
% 7.42/1.52  ------ Problem properties
% 7.42/1.52  
% 7.42/1.52  clauses:                                19
% 7.42/1.52  conjectures:                            1
% 7.42/1.52  epr:                                    1
% 7.42/1.52  horn:                                   19
% 7.42/1.52  ground:                                 1
% 7.42/1.52  unary:                                  6
% 7.42/1.52  binary:                                 7
% 7.42/1.52  lits:                                   38
% 7.42/1.52  lits_eq:                                13
% 7.42/1.52  fd_pure:                                0
% 7.42/1.52  fd_pseudo:                              0
% 7.42/1.52  fd_cond:                                0
% 7.42/1.52  fd_pseudo_cond:                         0
% 7.42/1.52  ac_symbols:                             0
% 7.42/1.52  
% 7.42/1.52  ------ Propositional Solver
% 7.42/1.52  
% 7.42/1.52  prop_solver_calls:                      29
% 7.42/1.52  prop_fast_solver_calls:                 672
% 7.42/1.52  smt_solver_calls:                       0
% 7.42/1.52  smt_fast_solver_calls:                  0
% 7.42/1.52  prop_num_of_clauses:                    5478
% 7.42/1.52  prop_preprocess_simplified:             11990
% 7.42/1.52  prop_fo_subsumed:                       7
% 7.42/1.52  prop_solver_time:                       0.
% 7.42/1.52  smt_solver_time:                        0.
% 7.42/1.52  smt_fast_solver_time:                   0.
% 7.42/1.52  prop_fast_solver_time:                  0.
% 7.42/1.52  prop_unsat_core_time:                   0.
% 7.42/1.52  
% 7.42/1.52  ------ QBF
% 7.42/1.52  
% 7.42/1.52  qbf_q_res:                              0
% 7.42/1.52  qbf_num_tautologies:                    0
% 7.42/1.52  qbf_prep_cycles:                        0
% 7.42/1.52  
% 7.42/1.52  ------ BMC1
% 7.42/1.52  
% 7.42/1.52  bmc1_current_bound:                     -1
% 7.42/1.52  bmc1_last_solved_bound:                 -1
% 7.42/1.52  bmc1_unsat_core_size:                   -1
% 7.42/1.52  bmc1_unsat_core_parents_size:           -1
% 7.42/1.52  bmc1_merge_next_fun:                    0
% 7.42/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.42/1.52  
% 7.42/1.52  ------ Instantiation
% 7.42/1.52  
% 7.42/1.52  inst_num_of_clauses:                    1687
% 7.42/1.52  inst_num_in_passive:                    646
% 7.42/1.52  inst_num_in_active:                     535
% 7.42/1.52  inst_num_in_unprocessed:                506
% 7.42/1.52  inst_num_of_loops:                      600
% 7.42/1.52  inst_num_of_learning_restarts:          0
% 7.42/1.52  inst_num_moves_active_passive:          63
% 7.42/1.52  inst_lit_activity:                      0
% 7.42/1.52  inst_lit_activity_moves:                1
% 7.42/1.52  inst_num_tautologies:                   0
% 7.42/1.52  inst_num_prop_implied:                  0
% 7.42/1.52  inst_num_existing_simplified:           0
% 7.42/1.52  inst_num_eq_res_simplified:             0
% 7.42/1.52  inst_num_child_elim:                    0
% 7.42/1.52  inst_num_of_dismatching_blockings:      488
% 7.42/1.52  inst_num_of_non_proper_insts:           1259
% 7.42/1.52  inst_num_of_duplicates:                 0
% 7.42/1.52  inst_inst_num_from_inst_to_res:         0
% 7.42/1.52  inst_dismatching_checking_time:         0.
% 7.42/1.52  
% 7.42/1.52  ------ Resolution
% 7.42/1.52  
% 7.42/1.52  res_num_of_clauses:                     0
% 7.42/1.52  res_num_in_passive:                     0
% 7.42/1.52  res_num_in_active:                      0
% 7.42/1.52  res_num_of_loops:                       110
% 7.42/1.52  res_forward_subset_subsumed:            138
% 7.42/1.52  res_backward_subset_subsumed:           2
% 7.42/1.52  res_forward_subsumed:                   0
% 7.42/1.52  res_backward_subsumed:                  0
% 7.42/1.52  res_forward_subsumption_resolution:     0
% 7.42/1.52  res_backward_subsumption_resolution:    0
% 7.42/1.52  res_clause_to_clause_subsumption:       2323
% 7.42/1.52  res_orphan_elimination:                 0
% 7.42/1.52  res_tautology_del:                      113
% 7.42/1.52  res_num_eq_res_simplified:              0
% 7.42/1.52  res_num_sel_changes:                    0
% 7.42/1.52  res_moves_from_active_to_pass:          0
% 7.42/1.52  
% 7.42/1.52  ------ Superposition
% 7.42/1.52  
% 7.42/1.52  sup_time_total:                         0.
% 7.42/1.52  sup_time_generating:                    0.
% 7.42/1.52  sup_time_sim_full:                      0.
% 7.42/1.52  sup_time_sim_immed:                     0.
% 7.42/1.52  
% 7.42/1.52  sup_num_of_clauses:                     403
% 7.42/1.52  sup_num_in_active:                      93
% 7.42/1.52  sup_num_in_passive:                     310
% 7.42/1.52  sup_num_of_loops:                       119
% 7.42/1.52  sup_fw_superposition:                   1015
% 7.42/1.52  sup_bw_superposition:                   1119
% 7.42/1.52  sup_immediate_simplified:               1805
% 7.42/1.52  sup_given_eliminated:                   1
% 7.42/1.52  comparisons_done:                       0
% 7.42/1.52  comparisons_avoided:                    0
% 7.42/1.52  
% 7.42/1.52  ------ Simplifications
% 7.42/1.52  
% 7.42/1.52  
% 7.42/1.52  sim_fw_subset_subsumed:                 4
% 7.42/1.52  sim_bw_subset_subsumed:                 2
% 7.42/1.52  sim_fw_subsumed:                        345
% 7.42/1.52  sim_bw_subsumed:                        0
% 7.42/1.52  sim_fw_subsumption_res:                 3
% 7.42/1.52  sim_bw_subsumption_res:                 0
% 7.42/1.52  sim_tautology_del:                      2
% 7.42/1.52  sim_eq_tautology_del:                   390
% 7.42/1.52  sim_eq_res_simp:                        0
% 7.42/1.52  sim_fw_demodulated:                     793
% 7.42/1.52  sim_bw_demodulated:                     51
% 7.42/1.52  sim_light_normalised:                   950
% 7.42/1.52  sim_joinable_taut:                      0
% 7.42/1.52  sim_joinable_simp:                      0
% 7.42/1.52  sim_ac_normalised:                      0
% 7.42/1.52  sim_smt_subsumption:                    0
% 7.42/1.52  
%------------------------------------------------------------------------------
