%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:43 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 919 expanded)
%              Number of clauses        :   55 ( 274 expanded)
%              Number of leaves         :   10 ( 224 expanded)
%              Depth                    :   30
%              Number of atoms          :  251 (2440 expanded)
%              Number of equality atoms :  141 (1093 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k6_subset_1(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f19])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f42])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,(
    k6_subset_1(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_276,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_326,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_276,c_9])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_269,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_270,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_307,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_270,c_9])).

cnf(c_878,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_269,c_307])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_272,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_292,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_272,c_9])).

cnf(c_885,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_878,c_292])).

cnf(c_4096,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_relat_1(k7_relat_1(sK2,X1)))) = X2
    | r2_hidden(sK0(X0,k1_relat_1(k7_relat_1(sK2,X1)),X2),X2) = iProver_top
    | r2_hidden(sK0(X0,k1_relat_1(k7_relat_1(sK2,X1)),X2),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_326,c_885])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_275,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_319,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_275,c_9])).

cnf(c_3873,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_relat_1(k7_relat_1(sK2,X2))
    | r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_319,c_885])).

cnf(c_7245,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X1))
    | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),k1_relat_1(sK2)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3873])).

cnf(c_7247,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X1))
    | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),k1_relat_1(sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7245])).

cnf(c_7250,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X1))
    | r2_hidden(sK0(k1_relat_1(sK2),X1,k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7247,c_878])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_277,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_333,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_277,c_9])).

cnf(c_8344,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X1))
    | k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X1))
    | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),X0) != iProver_top
    | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),k1_relat_1(k7_relat_1(sK2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7250,c_333])).

cnf(c_8349,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X1))
    | r2_hidden(sK0(k1_relat_1(sK2),X1,k1_relat_1(k7_relat_1(sK2,X0))),X1) != iProver_top
    | r2_hidden(sK0(k1_relat_1(sK2),X1,k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(k7_relat_1(sK2,X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8344,c_878])).

cnf(c_8697,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X1))
    | k1_setfam_1(k2_tarski(k1_relat_1(sK2),X1)) = k1_relat_1(k7_relat_1(sK2,X0))
    | r2_hidden(sK0(k1_relat_1(sK2),X1,k1_relat_1(k7_relat_1(sK2,X0))),X1) != iProver_top
    | r2_hidden(sK0(k1_relat_1(sK2),X1,k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_319,c_8349])).

cnf(c_8735,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X1))
    | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),X0) != iProver_top
    | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8697,c_878])).

cnf(c_9001,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4096,c_8735])).

cnf(c_9020,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9001,c_878])).

cnf(c_9401,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(k7_relat_1(sK2,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9020,c_333])).

cnf(c_9402,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(k7_relat_1(sK2,X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9401,c_878])).

cnf(c_9407,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(k7_relat_1(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_326,c_9402])).

cnf(c_9429,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
    | k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9407,c_9402])).

cnf(c_9430,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_9429,c_878])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_286,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_9])).

cnf(c_884,plain,
    ( k5_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_878,c_286])).

cnf(c_9718,plain,
    ( k5_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_9430,c_884])).

cnf(c_439,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9,c_9])).

cnf(c_883,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X0))) = k4_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_878,c_439])).

cnf(c_903,plain,
    ( k1_relat_1(k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),X0))) = k4_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(demodulation,[status(thm)],[c_883,c_878])).

cnf(c_9804,plain,
    ( k1_relat_1(k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),X0))) = k4_xboole_0(k1_relat_1(sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_9718,c_884,c_903])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1))) = k6_subset_1(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_271,plain,
    ( k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1))) = k6_subset_1(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_302,plain,
    ( k1_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X1))) = k4_xboole_0(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_271,c_8])).

cnf(c_643,plain,
    ( k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_269,c_302])).

cnf(c_12,negated_conjecture,
    ( k6_subset_1(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_289,plain,
    ( k4_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) ),
    inference(demodulation,[status(thm)],[c_12,c_8])).

cnf(c_993,plain,
    ( k4_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k4_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(demodulation,[status(thm)],[c_643,c_289])).

cnf(c_1832,plain,
    ( k1_relat_1(k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),sK1))) != k4_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(demodulation,[status(thm)],[c_903,c_993])).

cnf(c_10853,plain,
    ( k4_xboole_0(k1_relat_1(sK2),sK1) != k4_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(demodulation,[status(thm)],[c_9804,c_1832])).

cnf(c_10854,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10853])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:39:19 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 3.79/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.99  
% 3.79/0.99  ------  iProver source info
% 3.79/0.99  
% 3.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.99  git: non_committed_changes: false
% 3.79/0.99  git: last_make_outside_of_git: false
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  ------ Parsing...
% 3.79/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  ------ Proving...
% 3.79/0.99  ------ Problem Properties 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  clauses                                 14
% 3.79/0.99  conjectures                             2
% 3.79/0.99  EPR                                     1
% 3.79/0.99  Horn                                    12
% 3.79/0.99  unary                                   6
% 3.79/0.99  binary                                  4
% 3.79/0.99  lits                                    27
% 3.79/0.99  lits eq                                 10
% 3.79/0.99  fd_pure                                 0
% 3.79/0.99  fd_pseudo                               0
% 3.79/0.99  fd_cond                                 0
% 3.79/0.99  fd_pseudo_cond                          3
% 3.79/0.99  AC symbols                              0
% 3.79/0.99  
% 3.79/0.99  ------ Input Options Time Limit: Unbounded
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  Current options:
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS status Theorem for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99   Resolution empty clause
% 3.79/0.99  
% 3.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  fof(f1,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f14,plain,(
% 3.79/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.79/0.99    inference(nnf_transformation,[],[f1])).
% 3.79/0.99  
% 3.79/0.99  fof(f15,plain,(
% 3.79/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.79/0.99    inference(flattening,[],[f14])).
% 3.79/0.99  
% 3.79/0.99  fof(f16,plain,(
% 3.79/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.79/0.99    inference(rectify,[],[f15])).
% 3.79/0.99  
% 3.79/0.99  fof(f17,plain,(
% 3.79/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f18,plain,(
% 3.79/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 3.79/0.99  
% 3.79/0.99  fof(f25,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f18])).
% 3.79/0.99  
% 3.79/0.99  fof(f3,axiom,(
% 3.79/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f28,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f3])).
% 3.79/0.99  
% 3.79/0.99  fof(f38,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.79/0.99    inference(definition_unfolding,[],[f25,f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f6,axiom,(
% 3.79/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f31,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f6])).
% 3.79/0.99  
% 3.79/0.99  fof(f43,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.79/0.99    inference(definition_unfolding,[],[f31,f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f9,conjecture,(
% 3.79/0.99    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f10,negated_conjecture,(
% 3.79/0.99    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 3.79/0.99    inference(negated_conjecture,[],[f9])).
% 3.79/0.99  
% 3.79/0.99  fof(f13,plain,(
% 3.79/0.99    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 3.79/0.99    inference(ennf_transformation,[],[f10])).
% 3.79/0.99  
% 3.79/0.99  fof(f19,plain,(
% 3.79/0.99    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f20,plain,(
% 3.79/0.99    k6_subset_1(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f19])).
% 3.79/0.99  
% 3.79/0.99  fof(f34,plain,(
% 3.79/0.99    v1_relat_1(sK2)),
% 3.79/0.99    inference(cnf_transformation,[],[f20])).
% 3.79/0.99  
% 3.79/0.99  fof(f8,axiom,(
% 3.79/0.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f12,plain,(
% 3.79/0.99    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.79/0.99    inference(ennf_transformation,[],[f8])).
% 3.79/0.99  
% 3.79/0.99  fof(f33,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f12])).
% 3.79/0.99  
% 3.79/0.99  fof(f44,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.79/0.99    inference(definition_unfolding,[],[f33,f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f21,plain,(
% 3.79/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.79/0.99    inference(cnf_transformation,[],[f18])).
% 3.79/0.99  
% 3.79/0.99  fof(f42,plain,(
% 3.79/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 3.79/0.99    inference(definition_unfolding,[],[f21,f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f47,plain,(
% 3.79/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.79/0.99    inference(equality_resolution,[],[f42])).
% 3.79/0.99  
% 3.79/0.99  fof(f24,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f18])).
% 3.79/0.99  
% 3.79/0.99  fof(f39,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.79/0.99    inference(definition_unfolding,[],[f24,f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f26,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f18])).
% 3.79/0.99  
% 3.79/0.99  fof(f37,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.79/0.99    inference(definition_unfolding,[],[f26,f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f2,axiom,(
% 3.79/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f27,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f2])).
% 3.79/0.99  
% 3.79/0.99  fof(f36,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.79/0.99    inference(definition_unfolding,[],[f27,f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f7,axiom,(
% 3.79/0.99    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f11,plain,(
% 3.79/0.99    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.79/0.99    inference(ennf_transformation,[],[f7])).
% 3.79/0.99  
% 3.79/0.99  fof(f32,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f11])).
% 3.79/0.99  
% 3.79/0.99  fof(f5,axiom,(
% 3.79/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f30,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f5])).
% 3.79/0.99  
% 3.79/0.99  fof(f35,plain,(
% 3.79/0.99    k6_subset_1(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)))),
% 3.79/0.99    inference(cnf_transformation,[],[f20])).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2,plain,
% 3.79/0.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.79/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 3.79/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_276,plain,
% 3.79/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9,plain,
% 3.79/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_326,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_276,c_9]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_13,negated_conjecture,
% 3.79/0.99      ( v1_relat_1(sK2) ),
% 3.79/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_269,plain,
% 3.79/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11,plain,
% 3.79/0.99      ( ~ v1_relat_1(X0)
% 3.79/0.99      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_270,plain,
% 3.79/0.99      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_307,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_270,c_9]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_878,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_269,c_307]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6,plain,
% 3.79/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_272,plain,
% 3.79/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.79/0.99      | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_292,plain,
% 3.79/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.79/0.99      | r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) != iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_272,c_9]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_885,plain,
% 3.79/0.99      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) != iProver_top
% 3.79/0.99      | r2_hidden(X0,k1_relat_1(sK2)) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_878,c_292]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4096,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(X0,k1_relat_1(k7_relat_1(sK2,X1)))) = X2
% 3.79/0.99      | r2_hidden(sK0(X0,k1_relat_1(k7_relat_1(sK2,X1)),X2),X2) = iProver_top
% 3.79/0.99      | r2_hidden(sK0(X0,k1_relat_1(k7_relat_1(sK2,X1)),X2),k1_relat_1(sK2)) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_326,c_885]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3,plain,
% 3.79/0.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.79/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 3.79/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_275,plain,
% 3.79/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_319,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_275,c_9]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3873,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_relat_1(k7_relat_1(sK2,X2))
% 3.79/0.99      | r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),X0) = iProver_top
% 3.79/0.99      | r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),k1_relat_1(sK2)) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_319,c_885]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7245,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X1))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),k1_relat_1(sK2)) = iProver_top
% 3.79/0.99      | iProver_top != iProver_top ),
% 3.79/0.99      inference(equality_factoring,[status(thm)],[c_3873]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7247,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X1))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),k1_relat_1(sK2)) = iProver_top ),
% 3.79/0.99      inference(equality_resolution_simp,[status(thm)],[c_7245]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7250,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X1))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X1,k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(sK2)) = iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_7247,c_878]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1,plain,
% 3.79/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.79/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.79/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.79/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 3.79/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_277,plain,
% 3.79/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_333,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 3.79/0.99      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_277,c_9]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8344,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X1))
% 3.79/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK2),X0)) = k1_relat_1(k7_relat_1(sK2,X1))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),X0) != iProver_top
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),k1_relat_1(k7_relat_1(sK2,X1))) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_7250,c_333]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8349,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X1))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X1,k1_relat_1(k7_relat_1(sK2,X0))),X1) != iProver_top
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X1,k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(k7_relat_1(sK2,X0))) != iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_8344,c_878]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8697,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X1))
% 3.79/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK2),X1)) = k1_relat_1(k7_relat_1(sK2,X0))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X1,k1_relat_1(k7_relat_1(sK2,X0))),X1) != iProver_top
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X1,k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(sK2)) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_319,c_8349]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8735,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,X0)) = k1_relat_1(k7_relat_1(sK2,X1))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),X0) != iProver_top
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),X0,k1_relat_1(k7_relat_1(sK2,X1))),k1_relat_1(sK2)) = iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_8697,c_878]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9001,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 3.79/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(sK2)) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_4096,c_8735]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9020,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(sK2)) = iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_9001,c_878]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9401,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 3.79/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(k7_relat_1(sK2,X0))) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_9020,c_333]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9402,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(k7_relat_1(sK2,X0))) != iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_9401,c_878]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9407,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 3.79/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 3.79/0.99      | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))),k1_relat_1(k7_relat_1(sK2,X0))) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_326,c_9402]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9429,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0))
% 3.79/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 3.79/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_9407,c_9402]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9430,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) = k1_relat_1(k7_relat_1(sK2,X0)) ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_9429,c_878]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_0,plain,
% 3.79/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_286,plain,
% 3.79/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_0,c_9]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_884,plain,
% 3.79/0.99      ( k5_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_878,c_286]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9718,plain,
% 3.79/0.99      ( k5_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0))) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_9430,c_884]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_439,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_9,c_9]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_883,plain,
% 3.79/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X0))) = k4_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0))) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_878,c_439]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_903,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),X0))) = k4_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,X0))) ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_883,c_878]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9804,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),X0))) = k4_xboole_0(k1_relat_1(sK2),X0) ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_9718,c_884,c_903]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_10,plain,
% 3.79/0.99      ( ~ v1_relat_1(X0)
% 3.79/0.99      | k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1))) = k6_subset_1(k1_relat_1(X0),X1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_271,plain,
% 3.79/0.99      ( k1_relat_1(k6_subset_1(X0,k7_relat_1(X0,X1))) = k6_subset_1(k1_relat_1(X0),X1)
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8,plain,
% 3.79/0.99      ( k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
% 3.79/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_302,plain,
% 3.79/0.99      ( k1_relat_1(k4_xboole_0(X0,k7_relat_1(X0,X1))) = k4_xboole_0(k1_relat_1(X0),X1)
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_271,c_8]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_643,plain,
% 3.79/0.99      ( k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) = k4_xboole_0(k1_relat_1(sK2),X0) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_269,c_302]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_12,negated_conjecture,
% 3.79/0.99      ( k6_subset_1(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1))) ),
% 3.79/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_289,plain,
% 3.79/0.99      ( k4_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_12,c_8]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_993,plain,
% 3.79/0.99      ( k4_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) != k4_xboole_0(k1_relat_1(sK2),sK1) ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_643,c_289]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1832,plain,
% 3.79/0.99      ( k1_relat_1(k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),sK1))) != k4_xboole_0(k1_relat_1(sK2),sK1) ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_903,c_993]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_10853,plain,
% 3.79/0.99      ( k4_xboole_0(k1_relat_1(sK2),sK1) != k4_xboole_0(k1_relat_1(sK2),sK1) ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_9804,c_1832]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_10854,plain,
% 3.79/0.99      ( $false ),
% 3.79/0.99      inference(equality_resolution_simp,[status(thm)],[c_10853]) ).
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  ------                               Statistics
% 3.79/0.99  
% 3.79/0.99  ------ Selected
% 3.79/0.99  
% 3.79/0.99  total_time:                             0.414
% 3.79/0.99  
%------------------------------------------------------------------------------
