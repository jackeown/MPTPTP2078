%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:49 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 572 expanded)
%              Number of clauses        :   62 ( 173 expanded)
%              Number of leaves         :   18 ( 138 expanded)
%              Depth                    :   18
%              Number of atoms          :  190 ( 815 expanded)
%              Number of equality atoms :  122 ( 540 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f22,plain,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f35,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f36,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
        & v1_relat_1(X1) )
   => ( k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).

fof(f58,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f60])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f65,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f62,f62])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f62])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    k1_setfam_1(k4_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(definition_unfolding,[],[f59,f63])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_373,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_374,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_379,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1837,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,k1_relat_1(k6_relat_1(X0))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_374,c_379])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1845,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1837,c_9])).

cnf(c_1866,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_373,c_1845])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_381,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1090,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_374,c_381])).

cnf(c_3172,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) ),
    inference(superposition,[status(thm)],[c_1866,c_1090])).

cnf(c_3176,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_3172,c_1090])).

cnf(c_11,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_377,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_378,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1243,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_378])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1679,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1243,c_18])).

cnf(c_1680,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1679])).

cnf(c_1688,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(X0,X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k7_relat_1(X0,X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_377,c_1680])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_375,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_955,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_374,c_375])).

cnf(c_5275,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,X0))) = k6_relat_1(k1_relat_1(k7_relat_1(X1,X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1688,c_955])).

cnf(c_5283,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_373,c_5275])).

cnf(c_7272,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(superposition,[status(thm)],[c_5283,c_1090])).

cnf(c_7277,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_7272,c_8])).

cnf(c_21899,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3176,c_7277])).

cnf(c_1,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_385,plain,
    ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1687,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_385,c_1680])).

cnf(c_6762,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),k6_relat_1(X1)) = k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_1,c_1687])).

cnf(c_7117,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_6762,c_8])).

cnf(c_7139,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_7117,c_955,c_1090])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_383,plain,
    ( k9_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1982,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_374,c_383])).

cnf(c_1987,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1982,c_9])).

cnf(c_2258,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_1,c_1987])).

cnf(c_7140,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_7139,c_2258])).

cnf(c_9714,plain,
    ( k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_7140,c_2258])).

cnf(c_21925,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) ),
    inference(superposition,[status(thm)],[c_21899,c_9714])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_376,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1689,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(X0,X1))),k6_relat_1(k1_relat_1(X0))) = k6_relat_1(k1_relat_1(k7_relat_1(X0,X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_376,c_1680])).

cnf(c_7822,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(X0)),k1_relat_1(k7_relat_1(X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(X0,X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1689,c_955])).

cnf(c_7830,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_373,c_7822])).

cnf(c_10552,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(superposition,[status(thm)],[c_7830,c_1090])).

cnf(c_10557,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_10552,c_8])).

cnf(c_21945,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_21925,c_10557])).

cnf(c_956,plain,
    ( k5_relat_1(k6_relat_1(X0),sK1) = k7_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_373,c_375])).

cnf(c_15,negated_conjecture,
    ( k1_setfam_1(k4_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2536,plain,
    ( k1_setfam_1(k4_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_956,c_15])).

cnf(c_9711,plain,
    ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_7140,c_2536])).

cnf(c_22381,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_21945,c_9711])).

cnf(c_22382,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_22381])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:11:20 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.88/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.88/1.47  
% 7.88/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.88/1.47  
% 7.88/1.47  ------  iProver source info
% 7.88/1.47  
% 7.88/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.88/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.88/1.47  git: non_committed_changes: false
% 7.88/1.47  git: last_make_outside_of_git: false
% 7.88/1.47  
% 7.88/1.47  ------ 
% 7.88/1.47  
% 7.88/1.47  ------ Input Options
% 7.88/1.47  
% 7.88/1.47  --out_options                           all
% 7.88/1.47  --tptp_safe_out                         true
% 7.88/1.47  --problem_path                          ""
% 7.88/1.47  --include_path                          ""
% 7.88/1.47  --clausifier                            res/vclausify_rel
% 7.88/1.47  --clausifier_options                    --mode clausify
% 7.88/1.47  --stdin                                 false
% 7.88/1.47  --stats_out                             sel
% 7.88/1.47  
% 7.88/1.47  ------ General Options
% 7.88/1.47  
% 7.88/1.47  --fof                                   false
% 7.88/1.47  --time_out_real                         604.99
% 7.88/1.47  --time_out_virtual                      -1.
% 7.88/1.47  --symbol_type_check                     false
% 7.88/1.47  --clausify_out                          false
% 7.88/1.47  --sig_cnt_out                           false
% 7.88/1.47  --trig_cnt_out                          false
% 7.88/1.47  --trig_cnt_out_tolerance                1.
% 7.88/1.47  --trig_cnt_out_sk_spl                   false
% 7.88/1.47  --abstr_cl_out                          false
% 7.88/1.47  
% 7.88/1.47  ------ Global Options
% 7.88/1.47  
% 7.88/1.47  --schedule                              none
% 7.88/1.47  --add_important_lit                     false
% 7.88/1.47  --prop_solver_per_cl                    1000
% 7.88/1.47  --min_unsat_core                        false
% 7.88/1.47  --soft_assumptions                      false
% 7.88/1.47  --soft_lemma_size                       3
% 7.88/1.47  --prop_impl_unit_size                   0
% 7.88/1.47  --prop_impl_unit                        []
% 7.88/1.47  --share_sel_clauses                     true
% 7.88/1.47  --reset_solvers                         false
% 7.88/1.47  --bc_imp_inh                            [conj_cone]
% 7.88/1.47  --conj_cone_tolerance                   3.
% 7.88/1.47  --extra_neg_conj                        none
% 7.88/1.47  --large_theory_mode                     true
% 7.88/1.47  --prolific_symb_bound                   200
% 7.88/1.47  --lt_threshold                          2000
% 7.88/1.47  --clause_weak_htbl                      true
% 7.88/1.47  --gc_record_bc_elim                     false
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing Options
% 7.88/1.47  
% 7.88/1.47  --preprocessing_flag                    true
% 7.88/1.47  --time_out_prep_mult                    0.1
% 7.88/1.47  --splitting_mode                        input
% 7.88/1.47  --splitting_grd                         true
% 7.88/1.47  --splitting_cvd                         false
% 7.88/1.47  --splitting_cvd_svl                     false
% 7.88/1.47  --splitting_nvd                         32
% 7.88/1.47  --sub_typing                            true
% 7.88/1.47  --prep_gs_sim                           false
% 7.88/1.47  --prep_unflatten                        true
% 7.88/1.47  --prep_res_sim                          true
% 7.88/1.47  --prep_upred                            true
% 7.88/1.47  --prep_sem_filter                       exhaustive
% 7.88/1.47  --prep_sem_filter_out                   false
% 7.88/1.47  --pred_elim                             false
% 7.88/1.47  --res_sim_input                         true
% 7.88/1.47  --eq_ax_congr_red                       true
% 7.88/1.47  --pure_diseq_elim                       true
% 7.88/1.47  --brand_transform                       false
% 7.88/1.47  --non_eq_to_eq                          false
% 7.88/1.47  --prep_def_merge                        true
% 7.88/1.47  --prep_def_merge_prop_impl              false
% 7.88/1.47  --prep_def_merge_mbd                    true
% 7.88/1.47  --prep_def_merge_tr_red                 false
% 7.88/1.47  --prep_def_merge_tr_cl                  false
% 7.88/1.47  --smt_preprocessing                     true
% 7.88/1.47  --smt_ac_axioms                         fast
% 7.88/1.47  --preprocessed_out                      false
% 7.88/1.47  --preprocessed_stats                    false
% 7.88/1.47  
% 7.88/1.47  ------ Abstraction refinement Options
% 7.88/1.47  
% 7.88/1.47  --abstr_ref                             []
% 7.88/1.47  --abstr_ref_prep                        false
% 7.88/1.47  --abstr_ref_until_sat                   false
% 7.88/1.47  --abstr_ref_sig_restrict                funpre
% 7.88/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.47  --abstr_ref_under                       []
% 7.88/1.47  
% 7.88/1.47  ------ SAT Options
% 7.88/1.47  
% 7.88/1.47  --sat_mode                              false
% 7.88/1.47  --sat_fm_restart_options                ""
% 7.88/1.47  --sat_gr_def                            false
% 7.88/1.47  --sat_epr_types                         true
% 7.88/1.47  --sat_non_cyclic_types                  false
% 7.88/1.47  --sat_finite_models                     false
% 7.88/1.47  --sat_fm_lemmas                         false
% 7.88/1.47  --sat_fm_prep                           false
% 7.88/1.47  --sat_fm_uc_incr                        true
% 7.88/1.47  --sat_out_model                         small
% 7.88/1.47  --sat_out_clauses                       false
% 7.88/1.47  
% 7.88/1.47  ------ QBF Options
% 7.88/1.47  
% 7.88/1.47  --qbf_mode                              false
% 7.88/1.47  --qbf_elim_univ                         false
% 7.88/1.47  --qbf_dom_inst                          none
% 7.88/1.47  --qbf_dom_pre_inst                      false
% 7.88/1.47  --qbf_sk_in                             false
% 7.88/1.47  --qbf_pred_elim                         true
% 7.88/1.47  --qbf_split                             512
% 7.88/1.47  
% 7.88/1.47  ------ BMC1 Options
% 7.88/1.47  
% 7.88/1.47  --bmc1_incremental                      false
% 7.88/1.47  --bmc1_axioms                           reachable_all
% 7.88/1.47  --bmc1_min_bound                        0
% 7.88/1.47  --bmc1_max_bound                        -1
% 7.88/1.47  --bmc1_max_bound_default                -1
% 7.88/1.47  --bmc1_symbol_reachability              true
% 7.88/1.47  --bmc1_property_lemmas                  false
% 7.88/1.47  --bmc1_k_induction                      false
% 7.88/1.47  --bmc1_non_equiv_states                 false
% 7.88/1.47  --bmc1_deadlock                         false
% 7.88/1.47  --bmc1_ucm                              false
% 7.88/1.47  --bmc1_add_unsat_core                   none
% 7.88/1.47  --bmc1_unsat_core_children              false
% 7.88/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.47  --bmc1_out_stat                         full
% 7.88/1.47  --bmc1_ground_init                      false
% 7.88/1.47  --bmc1_pre_inst_next_state              false
% 7.88/1.47  --bmc1_pre_inst_state                   false
% 7.88/1.47  --bmc1_pre_inst_reach_state             false
% 7.88/1.47  --bmc1_out_unsat_core                   false
% 7.88/1.47  --bmc1_aig_witness_out                  false
% 7.88/1.47  --bmc1_verbose                          false
% 7.88/1.47  --bmc1_dump_clauses_tptp                false
% 7.88/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.47  --bmc1_dump_file                        -
% 7.88/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.47  --bmc1_ucm_extend_mode                  1
% 7.88/1.47  --bmc1_ucm_init_mode                    2
% 7.88/1.47  --bmc1_ucm_cone_mode                    none
% 7.88/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.47  --bmc1_ucm_relax_model                  4
% 7.88/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.47  --bmc1_ucm_layered_model                none
% 7.88/1.47  --bmc1_ucm_max_lemma_size               10
% 7.88/1.47  
% 7.88/1.47  ------ AIG Options
% 7.88/1.47  
% 7.88/1.47  --aig_mode                              false
% 7.88/1.47  
% 7.88/1.47  ------ Instantiation Options
% 7.88/1.47  
% 7.88/1.47  --instantiation_flag                    true
% 7.88/1.47  --inst_sos_flag                         false
% 7.88/1.47  --inst_sos_phase                        true
% 7.88/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.47  --inst_lit_sel_side                     num_symb
% 7.88/1.47  --inst_solver_per_active                1400
% 7.88/1.47  --inst_solver_calls_frac                1.
% 7.88/1.47  --inst_passive_queue_type               priority_queues
% 7.88/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.47  --inst_passive_queues_freq              [25;2]
% 7.88/1.47  --inst_dismatching                      true
% 7.88/1.47  --inst_eager_unprocessed_to_passive     true
% 7.88/1.47  --inst_prop_sim_given                   true
% 7.88/1.47  --inst_prop_sim_new                     false
% 7.88/1.47  --inst_subs_new                         false
% 7.88/1.47  --inst_eq_res_simp                      false
% 7.88/1.47  --inst_subs_given                       false
% 7.88/1.47  --inst_orphan_elimination               true
% 7.88/1.47  --inst_learning_loop_flag               true
% 7.88/1.47  --inst_learning_start                   3000
% 7.88/1.47  --inst_learning_factor                  2
% 7.88/1.47  --inst_start_prop_sim_after_learn       3
% 7.88/1.47  --inst_sel_renew                        solver
% 7.88/1.47  --inst_lit_activity_flag                true
% 7.88/1.47  --inst_restr_to_given                   false
% 7.88/1.47  --inst_activity_threshold               500
% 7.88/1.47  --inst_out_proof                        true
% 7.88/1.47  
% 7.88/1.47  ------ Resolution Options
% 7.88/1.47  
% 7.88/1.47  --resolution_flag                       true
% 7.88/1.47  --res_lit_sel                           adaptive
% 7.88/1.47  --res_lit_sel_side                      none
% 7.88/1.47  --res_ordering                          kbo
% 7.88/1.47  --res_to_prop_solver                    active
% 7.88/1.47  --res_prop_simpl_new                    false
% 7.88/1.47  --res_prop_simpl_given                  true
% 7.88/1.47  --res_passive_queue_type                priority_queues
% 7.88/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.47  --res_passive_queues_freq               [15;5]
% 7.88/1.47  --res_forward_subs                      full
% 7.88/1.47  --res_backward_subs                     full
% 7.88/1.47  --res_forward_subs_resolution           true
% 7.88/1.47  --res_backward_subs_resolution          true
% 7.88/1.47  --res_orphan_elimination                true
% 7.88/1.47  --res_time_limit                        2.
% 7.88/1.47  --res_out_proof                         true
% 7.88/1.47  
% 7.88/1.47  ------ Superposition Options
% 7.88/1.47  
% 7.88/1.47  --superposition_flag                    true
% 7.88/1.47  --sup_passive_queue_type                priority_queues
% 7.88/1.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.47  --sup_passive_queues_freq               [1;4]
% 7.88/1.47  --demod_completeness_check              fast
% 7.88/1.47  --demod_use_ground                      true
% 7.88/1.47  --sup_to_prop_solver                    passive
% 7.88/1.47  --sup_prop_simpl_new                    true
% 7.88/1.47  --sup_prop_simpl_given                  true
% 7.88/1.47  --sup_fun_splitting                     false
% 7.88/1.47  --sup_smt_interval                      50000
% 7.88/1.47  
% 7.88/1.47  ------ Superposition Simplification Setup
% 7.88/1.47  
% 7.88/1.47  --sup_indices_passive                   []
% 7.88/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.47  --sup_full_bw                           [BwDemod]
% 7.88/1.47  --sup_immed_triv                        [TrivRules]
% 7.88/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.47  --sup_immed_bw_main                     []
% 7.88/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.47  
% 7.88/1.47  ------ Combination Options
% 7.88/1.47  
% 7.88/1.47  --comb_res_mult                         3
% 7.88/1.47  --comb_sup_mult                         2
% 7.88/1.47  --comb_inst_mult                        10
% 7.88/1.47  
% 7.88/1.47  ------ Debug Options
% 7.88/1.47  
% 7.88/1.47  --dbg_backtrace                         false
% 7.88/1.47  --dbg_dump_prop_clauses                 false
% 7.88/1.47  --dbg_dump_prop_clauses_file            -
% 7.88/1.47  --dbg_out_stat                          false
% 7.88/1.47  ------ Parsing...
% 7.88/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.88/1.47  ------ Proving...
% 7.88/1.47  ------ Problem Properties 
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  clauses                                 17
% 7.88/1.47  conjectures                             2
% 7.88/1.47  EPR                                     1
% 7.88/1.47  Horn                                    17
% 7.88/1.47  unary                                   7
% 7.88/1.47  binary                                  7
% 7.88/1.47  lits                                    30
% 7.88/1.47  lits eq                                 11
% 7.88/1.47  fd_pure                                 0
% 7.88/1.47  fd_pseudo                               0
% 7.88/1.47  fd_cond                                 0
% 7.88/1.47  fd_pseudo_cond                          0
% 7.88/1.47  AC symbols                              0
% 7.88/1.47  
% 7.88/1.47  ------ Input Options Time Limit: Unbounded
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  ------ 
% 7.88/1.47  Current options:
% 7.88/1.47  ------ 
% 7.88/1.47  
% 7.88/1.47  ------ Input Options
% 7.88/1.47  
% 7.88/1.47  --out_options                           all
% 7.88/1.47  --tptp_safe_out                         true
% 7.88/1.47  --problem_path                          ""
% 7.88/1.47  --include_path                          ""
% 7.88/1.47  --clausifier                            res/vclausify_rel
% 7.88/1.47  --clausifier_options                    --mode clausify
% 7.88/1.47  --stdin                                 false
% 7.88/1.47  --stats_out                             sel
% 7.88/1.47  
% 7.88/1.47  ------ General Options
% 7.88/1.47  
% 7.88/1.47  --fof                                   false
% 7.88/1.47  --time_out_real                         604.99
% 7.88/1.47  --time_out_virtual                      -1.
% 7.88/1.47  --symbol_type_check                     false
% 7.88/1.47  --clausify_out                          false
% 7.88/1.47  --sig_cnt_out                           false
% 7.88/1.47  --trig_cnt_out                          false
% 7.88/1.47  --trig_cnt_out_tolerance                1.
% 7.88/1.47  --trig_cnt_out_sk_spl                   false
% 7.88/1.47  --abstr_cl_out                          false
% 7.88/1.47  
% 7.88/1.47  ------ Global Options
% 7.88/1.47  
% 7.88/1.47  --schedule                              none
% 7.88/1.47  --add_important_lit                     false
% 7.88/1.47  --prop_solver_per_cl                    1000
% 7.88/1.47  --min_unsat_core                        false
% 7.88/1.47  --soft_assumptions                      false
% 7.88/1.47  --soft_lemma_size                       3
% 7.88/1.47  --prop_impl_unit_size                   0
% 7.88/1.47  --prop_impl_unit                        []
% 7.88/1.47  --share_sel_clauses                     true
% 7.88/1.47  --reset_solvers                         false
% 7.88/1.47  --bc_imp_inh                            [conj_cone]
% 7.88/1.47  --conj_cone_tolerance                   3.
% 7.88/1.47  --extra_neg_conj                        none
% 7.88/1.47  --large_theory_mode                     true
% 7.88/1.47  --prolific_symb_bound                   200
% 7.88/1.47  --lt_threshold                          2000
% 7.88/1.47  --clause_weak_htbl                      true
% 7.88/1.47  --gc_record_bc_elim                     false
% 7.88/1.47  
% 7.88/1.47  ------ Preprocessing Options
% 7.88/1.47  
% 7.88/1.47  --preprocessing_flag                    true
% 7.88/1.47  --time_out_prep_mult                    0.1
% 7.88/1.47  --splitting_mode                        input
% 7.88/1.47  --splitting_grd                         true
% 7.88/1.47  --splitting_cvd                         false
% 7.88/1.47  --splitting_cvd_svl                     false
% 7.88/1.47  --splitting_nvd                         32
% 7.88/1.47  --sub_typing                            true
% 7.88/1.47  --prep_gs_sim                           false
% 7.88/1.47  --prep_unflatten                        true
% 7.88/1.47  --prep_res_sim                          true
% 7.88/1.47  --prep_upred                            true
% 7.88/1.47  --prep_sem_filter                       exhaustive
% 7.88/1.47  --prep_sem_filter_out                   false
% 7.88/1.47  --pred_elim                             false
% 7.88/1.47  --res_sim_input                         true
% 7.88/1.47  --eq_ax_congr_red                       true
% 7.88/1.47  --pure_diseq_elim                       true
% 7.88/1.47  --brand_transform                       false
% 7.88/1.47  --non_eq_to_eq                          false
% 7.88/1.47  --prep_def_merge                        true
% 7.88/1.47  --prep_def_merge_prop_impl              false
% 7.88/1.47  --prep_def_merge_mbd                    true
% 7.88/1.47  --prep_def_merge_tr_red                 false
% 7.88/1.47  --prep_def_merge_tr_cl                  false
% 7.88/1.47  --smt_preprocessing                     true
% 7.88/1.47  --smt_ac_axioms                         fast
% 7.88/1.47  --preprocessed_out                      false
% 7.88/1.47  --preprocessed_stats                    false
% 7.88/1.47  
% 7.88/1.47  ------ Abstraction refinement Options
% 7.88/1.47  
% 7.88/1.47  --abstr_ref                             []
% 7.88/1.47  --abstr_ref_prep                        false
% 7.88/1.47  --abstr_ref_until_sat                   false
% 7.88/1.47  --abstr_ref_sig_restrict                funpre
% 7.88/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.88/1.47  --abstr_ref_under                       []
% 7.88/1.47  
% 7.88/1.47  ------ SAT Options
% 7.88/1.47  
% 7.88/1.47  --sat_mode                              false
% 7.88/1.47  --sat_fm_restart_options                ""
% 7.88/1.47  --sat_gr_def                            false
% 7.88/1.47  --sat_epr_types                         true
% 7.88/1.47  --sat_non_cyclic_types                  false
% 7.88/1.47  --sat_finite_models                     false
% 7.88/1.47  --sat_fm_lemmas                         false
% 7.88/1.47  --sat_fm_prep                           false
% 7.88/1.47  --sat_fm_uc_incr                        true
% 7.88/1.47  --sat_out_model                         small
% 7.88/1.47  --sat_out_clauses                       false
% 7.88/1.47  
% 7.88/1.47  ------ QBF Options
% 7.88/1.47  
% 7.88/1.47  --qbf_mode                              false
% 7.88/1.47  --qbf_elim_univ                         false
% 7.88/1.47  --qbf_dom_inst                          none
% 7.88/1.47  --qbf_dom_pre_inst                      false
% 7.88/1.47  --qbf_sk_in                             false
% 7.88/1.47  --qbf_pred_elim                         true
% 7.88/1.47  --qbf_split                             512
% 7.88/1.47  
% 7.88/1.47  ------ BMC1 Options
% 7.88/1.47  
% 7.88/1.47  --bmc1_incremental                      false
% 7.88/1.47  --bmc1_axioms                           reachable_all
% 7.88/1.47  --bmc1_min_bound                        0
% 7.88/1.47  --bmc1_max_bound                        -1
% 7.88/1.47  --bmc1_max_bound_default                -1
% 7.88/1.47  --bmc1_symbol_reachability              true
% 7.88/1.47  --bmc1_property_lemmas                  false
% 7.88/1.47  --bmc1_k_induction                      false
% 7.88/1.47  --bmc1_non_equiv_states                 false
% 7.88/1.47  --bmc1_deadlock                         false
% 7.88/1.47  --bmc1_ucm                              false
% 7.88/1.47  --bmc1_add_unsat_core                   none
% 7.88/1.47  --bmc1_unsat_core_children              false
% 7.88/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.88/1.47  --bmc1_out_stat                         full
% 7.88/1.47  --bmc1_ground_init                      false
% 7.88/1.47  --bmc1_pre_inst_next_state              false
% 7.88/1.47  --bmc1_pre_inst_state                   false
% 7.88/1.47  --bmc1_pre_inst_reach_state             false
% 7.88/1.47  --bmc1_out_unsat_core                   false
% 7.88/1.47  --bmc1_aig_witness_out                  false
% 7.88/1.47  --bmc1_verbose                          false
% 7.88/1.47  --bmc1_dump_clauses_tptp                false
% 7.88/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.88/1.47  --bmc1_dump_file                        -
% 7.88/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.88/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.88/1.47  --bmc1_ucm_extend_mode                  1
% 7.88/1.47  --bmc1_ucm_init_mode                    2
% 7.88/1.47  --bmc1_ucm_cone_mode                    none
% 7.88/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.88/1.47  --bmc1_ucm_relax_model                  4
% 7.88/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.88/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.88/1.47  --bmc1_ucm_layered_model                none
% 7.88/1.47  --bmc1_ucm_max_lemma_size               10
% 7.88/1.47  
% 7.88/1.47  ------ AIG Options
% 7.88/1.47  
% 7.88/1.47  --aig_mode                              false
% 7.88/1.47  
% 7.88/1.47  ------ Instantiation Options
% 7.88/1.47  
% 7.88/1.47  --instantiation_flag                    true
% 7.88/1.47  --inst_sos_flag                         false
% 7.88/1.47  --inst_sos_phase                        true
% 7.88/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.88/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.88/1.47  --inst_lit_sel_side                     num_symb
% 7.88/1.47  --inst_solver_per_active                1400
% 7.88/1.47  --inst_solver_calls_frac                1.
% 7.88/1.47  --inst_passive_queue_type               priority_queues
% 7.88/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.88/1.47  --inst_passive_queues_freq              [25;2]
% 7.88/1.47  --inst_dismatching                      true
% 7.88/1.47  --inst_eager_unprocessed_to_passive     true
% 7.88/1.47  --inst_prop_sim_given                   true
% 7.88/1.47  --inst_prop_sim_new                     false
% 7.88/1.47  --inst_subs_new                         false
% 7.88/1.47  --inst_eq_res_simp                      false
% 7.88/1.47  --inst_subs_given                       false
% 7.88/1.47  --inst_orphan_elimination               true
% 7.88/1.47  --inst_learning_loop_flag               true
% 7.88/1.47  --inst_learning_start                   3000
% 7.88/1.47  --inst_learning_factor                  2
% 7.88/1.47  --inst_start_prop_sim_after_learn       3
% 7.88/1.47  --inst_sel_renew                        solver
% 7.88/1.47  --inst_lit_activity_flag                true
% 7.88/1.47  --inst_restr_to_given                   false
% 7.88/1.47  --inst_activity_threshold               500
% 7.88/1.47  --inst_out_proof                        true
% 7.88/1.47  
% 7.88/1.47  ------ Resolution Options
% 7.88/1.47  
% 7.88/1.47  --resolution_flag                       true
% 7.88/1.47  --res_lit_sel                           adaptive
% 7.88/1.47  --res_lit_sel_side                      none
% 7.88/1.47  --res_ordering                          kbo
% 7.88/1.47  --res_to_prop_solver                    active
% 7.88/1.47  --res_prop_simpl_new                    false
% 7.88/1.47  --res_prop_simpl_given                  true
% 7.88/1.47  --res_passive_queue_type                priority_queues
% 7.88/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.88/1.47  --res_passive_queues_freq               [15;5]
% 7.88/1.47  --res_forward_subs                      full
% 7.88/1.47  --res_backward_subs                     full
% 7.88/1.47  --res_forward_subs_resolution           true
% 7.88/1.47  --res_backward_subs_resolution          true
% 7.88/1.47  --res_orphan_elimination                true
% 7.88/1.47  --res_time_limit                        2.
% 7.88/1.47  --res_out_proof                         true
% 7.88/1.47  
% 7.88/1.47  ------ Superposition Options
% 7.88/1.47  
% 7.88/1.47  --superposition_flag                    true
% 7.88/1.47  --sup_passive_queue_type                priority_queues
% 7.88/1.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.88/1.47  --sup_passive_queues_freq               [1;4]
% 7.88/1.47  --demod_completeness_check              fast
% 7.88/1.47  --demod_use_ground                      true
% 7.88/1.47  --sup_to_prop_solver                    passive
% 7.88/1.47  --sup_prop_simpl_new                    true
% 7.88/1.47  --sup_prop_simpl_given                  true
% 7.88/1.47  --sup_fun_splitting                     false
% 7.88/1.47  --sup_smt_interval                      50000
% 7.88/1.47  
% 7.88/1.47  ------ Superposition Simplification Setup
% 7.88/1.47  
% 7.88/1.47  --sup_indices_passive                   []
% 7.88/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.88/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.88/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.47  --sup_full_bw                           [BwDemod]
% 7.88/1.47  --sup_immed_triv                        [TrivRules]
% 7.88/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.88/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.47  --sup_immed_bw_main                     []
% 7.88/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.88/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.88/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.88/1.47  
% 7.88/1.47  ------ Combination Options
% 7.88/1.47  
% 7.88/1.47  --comb_res_mult                         3
% 7.88/1.47  --comb_sup_mult                         2
% 7.88/1.47  --comb_inst_mult                        10
% 7.88/1.47  
% 7.88/1.47  ------ Debug Options
% 7.88/1.47  
% 7.88/1.47  --dbg_backtrace                         false
% 7.88/1.47  --dbg_dump_prop_clauses                 false
% 7.88/1.47  --dbg_dump_prop_clauses_file            -
% 7.88/1.47  --dbg_out_stat                          false
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  ------ Proving...
% 7.88/1.47  
% 7.88/1.47  
% 7.88/1.47  % SZS status Theorem for theBenchmark.p
% 7.88/1.47  
% 7.88/1.47   Resolution empty clause
% 7.88/1.47  
% 7.88/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.88/1.47  
% 7.88/1.47  fof(f20,conjecture,(
% 7.88/1.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f21,negated_conjecture,(
% 7.88/1.47    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 7.88/1.47    inference(negated_conjecture,[],[f20])).
% 7.88/1.47  
% 7.88/1.47  fof(f22,plain,(
% 7.88/1.47    ~! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)))),
% 7.88/1.47    inference(pure_predicate_removal,[],[f21])).
% 7.88/1.47  
% 7.88/1.47  fof(f35,plain,(
% 7.88/1.47    ? [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) & v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f22])).
% 7.88/1.47  
% 7.88/1.47  fof(f36,plain,(
% 7.88/1.47    ? [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) & v1_relat_1(X1)) => (k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) & v1_relat_1(sK1))),
% 7.88/1.47    introduced(choice_axiom,[])).
% 7.88/1.47  
% 7.88/1.47  fof(f37,plain,(
% 7.88/1.47    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) & v1_relat_1(sK1)),
% 7.88/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).
% 7.88/1.47  
% 7.88/1.47  fof(f58,plain,(
% 7.88/1.47    v1_relat_1(sK1)),
% 7.88/1.47    inference(cnf_transformation,[],[f37])).
% 7.88/1.47  
% 7.88/1.47  fof(f19,axiom,(
% 7.88/1.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f23,plain,(
% 7.88/1.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 7.88/1.47    inference(pure_predicate_removal,[],[f19])).
% 7.88/1.47  
% 7.88/1.47  fof(f57,plain,(
% 7.88/1.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.88/1.47    inference(cnf_transformation,[],[f23])).
% 7.88/1.47  
% 7.88/1.47  fof(f13,axiom,(
% 7.88/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f29,plain,(
% 7.88/1.47    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.88/1.47    inference(ennf_transformation,[],[f13])).
% 7.88/1.47  
% 7.88/1.47  fof(f50,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f29])).
% 7.88/1.47  
% 7.88/1.47  fof(f14,axiom,(
% 7.88/1.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f51,plain,(
% 7.88/1.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.88/1.47    inference(cnf_transformation,[],[f14])).
% 7.88/1.47  
% 7.88/1.47  fof(f11,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f27,plain,(
% 7.88/1.47    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f11])).
% 7.88/1.47  
% 7.88/1.47  fof(f48,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f27])).
% 7.88/1.47  
% 7.88/1.47  fof(f16,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f32,plain,(
% 7.88/1.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f16])).
% 7.88/1.47  
% 7.88/1.47  fof(f54,plain,(
% 7.88/1.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f32])).
% 7.88/1.47  
% 7.88/1.47  fof(f52,plain,(
% 7.88/1.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.88/1.47    inference(cnf_transformation,[],[f14])).
% 7.88/1.47  
% 7.88/1.47  fof(f15,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f30,plain,(
% 7.88/1.47    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f15])).
% 7.88/1.47  
% 7.88/1.47  fof(f31,plain,(
% 7.88/1.47    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(flattening,[],[f30])).
% 7.88/1.47  
% 7.88/1.47  fof(f53,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f31])).
% 7.88/1.47  
% 7.88/1.47  fof(f18,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f34,plain,(
% 7.88/1.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f18])).
% 7.88/1.47  
% 7.88/1.47  fof(f56,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f34])).
% 7.88/1.47  
% 7.88/1.47  fof(f2,axiom,(
% 7.88/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f39,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f2])).
% 7.88/1.47  
% 7.88/1.47  fof(f3,axiom,(
% 7.88/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f40,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f3])).
% 7.88/1.47  
% 7.88/1.47  fof(f4,axiom,(
% 7.88/1.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f41,plain,(
% 7.88/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f4])).
% 7.88/1.47  
% 7.88/1.47  fof(f5,axiom,(
% 7.88/1.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f42,plain,(
% 7.88/1.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f5])).
% 7.88/1.47  
% 7.88/1.47  fof(f6,axiom,(
% 7.88/1.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f43,plain,(
% 7.88/1.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f6])).
% 7.88/1.47  
% 7.88/1.47  fof(f60,plain,(
% 7.88/1.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f42,f43])).
% 7.88/1.47  
% 7.88/1.47  fof(f61,plain,(
% 7.88/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f41,f60])).
% 7.88/1.47  
% 7.88/1.47  fof(f62,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f40,f61])).
% 7.88/1.47  
% 7.88/1.47  fof(f65,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f39,f62,f62])).
% 7.88/1.47  
% 7.88/1.47  fof(f1,axiom,(
% 7.88/1.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f38,plain,(
% 7.88/1.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f1])).
% 7.88/1.47  
% 7.88/1.47  fof(f7,axiom,(
% 7.88/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f44,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.88/1.47    inference(cnf_transformation,[],[f7])).
% 7.88/1.47  
% 7.88/1.47  fof(f63,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 7.88/1.47    inference(definition_unfolding,[],[f44,f62])).
% 7.88/1.47  
% 7.88/1.47  fof(f64,plain,(
% 7.88/1.47    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f38,f63])).
% 7.88/1.47  
% 7.88/1.47  fof(f9,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f25,plain,(
% 7.88/1.47    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f9])).
% 7.88/1.47  
% 7.88/1.47  fof(f46,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f25])).
% 7.88/1.47  
% 7.88/1.47  fof(f66,plain,(
% 7.88/1.47    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k1_setfam_1(k4_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(definition_unfolding,[],[f46,f63])).
% 7.88/1.47  
% 7.88/1.47  fof(f17,axiom,(
% 7.88/1.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 7.88/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.88/1.47  
% 7.88/1.47  fof(f33,plain,(
% 7.88/1.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.88/1.47    inference(ennf_transformation,[],[f17])).
% 7.88/1.47  
% 7.88/1.47  fof(f55,plain,(
% 7.88/1.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.88/1.47    inference(cnf_transformation,[],[f33])).
% 7.88/1.47  
% 7.88/1.47  fof(f59,plain,(
% 7.88/1.47    k3_xboole_0(k1_relat_1(sK1),sK0) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 7.88/1.47    inference(cnf_transformation,[],[f37])).
% 7.88/1.47  
% 7.88/1.47  fof(f67,plain,(
% 7.88/1.47    k1_setfam_1(k4_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 7.88/1.47    inference(definition_unfolding,[],[f59,f63])).
% 7.88/1.47  
% 7.88/1.47  cnf(c_16,negated_conjecture,
% 7.88/1.47      ( v1_relat_1(sK1) ),
% 7.88/1.47      inference(cnf_transformation,[],[f58]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_373,plain,
% 7.88/1.47      ( v1_relat_1(sK1) = iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_14,plain,
% 7.88/1.47      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.88/1.47      inference(cnf_transformation,[],[f57]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_374,plain,
% 7.88/1.47      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_7,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0)
% 7.88/1.47      | ~ v1_relat_1(X1)
% 7.88/1.47      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1)) ),
% 7.88/1.47      inference(cnf_transformation,[],[f50]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_379,plain,
% 7.88/1.47      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
% 7.88/1.47      | v1_relat_1(X0) != iProver_top
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1837,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,k1_relat_1(k6_relat_1(X0))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_374,c_379]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_9,plain,
% 7.88/1.47      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.88/1.47      inference(cnf_transformation,[],[f51]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1845,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(light_normalisation,[status(thm)],[c_1837,c_9]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1866,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_373,c_1845]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.88/1.47      inference(cnf_transformation,[],[f48]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_381,plain,
% 7.88/1.47      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1090,plain,
% 7.88/1.47      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_374,c_381]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3172,plain,
% 7.88/1.47      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_1866,c_1090]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_3176,plain,
% 7.88/1.47      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_3172,c_1090]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_11,plain,
% 7.88/1.47      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.88/1.47      inference(cnf_transformation,[],[f54]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_377,plain,
% 7.88/1.47      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_8,plain,
% 7.88/1.47      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.88/1.47      inference(cnf_transformation,[],[f52]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_10,plain,
% 7.88/1.47      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.88/1.47      | ~ v1_relat_1(X0)
% 7.88/1.47      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 7.88/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_378,plain,
% 7.88/1.47      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 7.88/1.47      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1243,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 7.88/1.47      | r1_tarski(X0,X1) != iProver_top
% 7.88/1.47      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_8,c_378]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_18,plain,
% 7.88/1.47      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1679,plain,
% 7.88/1.47      ( r1_tarski(X0,X1) != iProver_top
% 7.88/1.47      | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
% 7.88/1.47      inference(global_propositional_subsumption,[status(thm)],[c_1243,c_18]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1680,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 7.88/1.47      | r1_tarski(X0,X1) != iProver_top ),
% 7.88/1.47      inference(renaming,[status(thm)],[c_1679]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_1688,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(X0,X1))),k6_relat_1(X1)) = k6_relat_1(k1_relat_1(k7_relat_1(X0,X1)))
% 7.88/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_377,c_1680]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_13,plain,
% 7.88/1.47      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.88/1.47      inference(cnf_transformation,[],[f56]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_375,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_955,plain,
% 7.88/1.47      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_374,c_375]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5275,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,X0))) = k6_relat_1(k1_relat_1(k7_relat_1(X1,X0)))
% 7.88/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.88/1.47      inference(demodulation,[status(thm)],[c_1688,c_955]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_5283,plain,
% 7.88/1.47      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))) ),
% 7.88/1.47      inference(superposition,[status(thm)],[c_373,c_5275]) ).
% 7.88/1.47  
% 7.88/1.47  cnf(c_7272,plain,
% 7.88/1.47      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0)))) ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_5283,c_1090]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_7277,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 7.88/1.48      inference(demodulation,[status(thm)],[c_7272,c_8]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_21899,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 7.88/1.48      inference(light_normalisation,[status(thm)],[c_3176,c_7277]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_1,plain,
% 7.88/1.48      ( k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
% 7.88/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_0,plain,
% 7.88/1.48      ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
% 7.88/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_385,plain,
% 7.88/1.48      ( r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) = iProver_top ),
% 7.88/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_1687,plain,
% 7.88/1.48      ( k5_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_385,c_1680]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_6762,plain,
% 7.88/1.48      ( k5_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),k6_relat_1(X1)) = k6_relat_1(k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_1,c_1687]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_7117,plain,
% 7.88/1.48      ( k2_relat_1(k5_relat_1(k6_relat_1(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))),k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_6762,c_8]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_7139,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
% 7.88/1.48      inference(demodulation,[status(thm)],[c_7117,c_955,c_1090]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_3,plain,
% 7.88/1.48      ( ~ v1_relat_1(X0)
% 7.88/1.48      | k9_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k9_relat_1(X0,X1) ),
% 7.88/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_383,plain,
% 7.88/1.48      ( k9_relat_1(X0,k1_setfam_1(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1))) = k9_relat_1(X0,X1)
% 7.88/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_1982,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) = k9_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_374,c_383]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_1987,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k9_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.48      inference(light_normalisation,[status(thm)],[c_1982,c_9]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_2258,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(X0),k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) = k9_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_1,c_1987]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_7140,plain,
% 7.88/1.48      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.48      inference(light_normalisation,[status(thm)],[c_7139,c_2258]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_9714,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X1),X0)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 7.88/1.48      inference(demodulation,[status(thm)],[c_7140,c_2258]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_21925,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_21899,c_9714]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_12,plain,
% 7.88/1.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 7.88/1.48      | ~ v1_relat_1(X0) ),
% 7.88/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_376,plain,
% 7.88/1.48      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 7.88/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_1689,plain,
% 7.88/1.48      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(X0,X1))),k6_relat_1(k1_relat_1(X0))) = k6_relat_1(k1_relat_1(k7_relat_1(X0,X1)))
% 7.88/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_376,c_1680]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_7822,plain,
% 7.88/1.48      ( k7_relat_1(k6_relat_1(k1_relat_1(X0)),k1_relat_1(k7_relat_1(X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(X0,X1)))
% 7.88/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.88/1.48      inference(demodulation,[status(thm)],[c_1689,c_955]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_7830,plain,
% 7.88/1.48      ( k7_relat_1(k6_relat_1(k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0))) ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_373,c_7822]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_10552,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK1,X0)))) ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_7830,c_1090]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_10557,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 7.88/1.48      inference(demodulation,[status(thm)],[c_10552,c_8]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_21945,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),X0) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 7.88/1.48      inference(light_normalisation,[status(thm)],[c_21925,c_10557]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_956,plain,
% 7.88/1.48      ( k5_relat_1(k6_relat_1(X0),sK1) = k7_relat_1(sK1,X0) ),
% 7.88/1.48      inference(superposition,[status(thm)],[c_373,c_375]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_15,negated_conjecture,
% 7.88/1.48      ( k1_setfam_1(k4_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) != k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
% 7.88/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_2536,plain,
% 7.88/1.48      ( k1_setfam_1(k4_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 7.88/1.48      inference(demodulation,[status(thm)],[c_956,c_15]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_9711,plain,
% 7.88/1.48      ( k9_relat_1(k6_relat_1(k1_relat_1(sK1)),sK0) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 7.88/1.48      inference(demodulation,[status(thm)],[c_7140,c_2536]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_22381,plain,
% 7.88/1.48      ( k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 7.88/1.48      inference(demodulation,[status(thm)],[c_21945,c_9711]) ).
% 7.88/1.48  
% 7.88/1.48  cnf(c_22382,plain,
% 7.88/1.48      ( $false ),
% 7.88/1.48      inference(equality_resolution_simp,[status(thm)],[c_22381]) ).
% 7.88/1.48  
% 7.88/1.48  
% 7.88/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.88/1.48  
% 7.88/1.48  ------                               Statistics
% 7.88/1.48  
% 7.88/1.48  ------ Selected
% 7.88/1.48  
% 7.88/1.48  total_time:                             0.799
% 7.88/1.48  
%------------------------------------------------------------------------------
