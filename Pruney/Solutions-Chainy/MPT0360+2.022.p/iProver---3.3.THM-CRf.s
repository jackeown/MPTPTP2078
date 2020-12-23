%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:17 EST 2020

% Result     : Theorem 7.33s
% Output     : CNFRefutation 7.33s
% Verified   : 
% Statistics : Number of formulae       :  118 (3272 expanded)
%              Number of clauses        :   73 ( 894 expanded)
%              Number of leaves         :   11 ( 690 expanded)
%              Depth                    :   32
%              Number of atoms          :  313 (16285 expanded)
%              Number of equality atoms :  157 (4030 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK2
      & r1_tarski(sK2,k3_subset_1(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k1_xboole_0 != sK2
    & r1_tarski(sK2,k3_subset_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f20])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f36,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f23,f31])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f37,plain,(
    r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_161,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_162,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_161])).

cnf(c_591,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_162])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_482,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_473,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_476,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_738,plain,
    ( k3_xboole_0(sK2,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_473,c_476])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_481,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1062,plain,
    ( r2_hidden(X0,k5_xboole_0(sK2,sK2)) = iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_481])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_480,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_930,plain,
    ( r2_hidden(X0,k3_subset_1(sK1,sK3)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_480])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_474,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_737,plain,
    ( k3_xboole_0(sK2,k3_subset_1(sK1,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_474,c_476])).

cnf(c_1140,plain,
    ( r2_hidden(X0,k3_subset_1(sK1,sK3)) = iProver_top
    | r2_hidden(X0,k5_xboole_0(sK2,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_481])).

cnf(c_2078,plain,
    ( r2_hidden(X0,k5_xboole_0(sK2,sK2)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_930,c_1140])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_479,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_809,plain,
    ( r2_hidden(X0,k3_subset_1(sK1,sK3)) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_479])).

cnf(c_1224,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = X1
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),X1) = iProver_top
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_482,c_809])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_483,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2480,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = X0
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),sK1,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1224,c_483])).

cnf(c_1063,plain,
    ( r2_hidden(X0,k5_xboole_0(sK2,sK2)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_479])).

cnf(c_2766,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(sK2,sK2)
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),sK1,k5_xboole_0(sK2,sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2480,c_1063])).

cnf(c_2757,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),sK1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2480,c_479])).

cnf(c_2758,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | r2_hidden(sK0(k3_subset_1(sK1,sK3),sK1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2480,c_480])).

cnf(c_6424,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2757,c_2758])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_477,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_735,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_477,c_476])).

cnf(c_6452,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_6424,c_735])).

cnf(c_6481,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_6452])).

cnf(c_7868,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2766,c_6481])).

cnf(c_7948,plain,
    ( r2_hidden(X0,k3_subset_1(sK1,sK3)) = iProver_top
    | r2_hidden(X0,k5_xboole_0(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7868,c_479])).

cnf(c_1142,plain,
    ( r2_hidden(X0,k3_subset_1(sK1,sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_480])).

cnf(c_8077,plain,
    ( r2_hidden(X0,k5_xboole_0(sK2,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7948,c_1142])).

cnf(c_8084,plain,
    ( r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2078,c_8077])).

cnf(c_8644,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK2
    | r2_hidden(sK0(X0,X1,sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_482,c_8084])).

cnf(c_9277,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = sK2
    | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8644,c_479])).

cnf(c_9599,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = sK2
    | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9277,c_483])).

cnf(c_10417,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9599,c_8084])).

cnf(c_10425,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_591,c_10417])).

cnf(c_1019,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = X3
    | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,X3),X3) = iProver_top
    | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,X3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_482,c_479])).

cnf(c_21972,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)),k3_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)),X0)) = X1
    | r2_hidden(sK0(k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)),X0,X1),k3_subset_1(sK1,sK3)) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_10425,c_1019])).

cnf(c_22207,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = X1
    | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK2,X0,X1),k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21972,c_10425])).

cnf(c_22808,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k3_subset_1(sK1,sK3))) = X0
    | r2_hidden(sK0(sK2,k3_subset_1(sK1,sK3),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_22207,c_483])).

cnf(c_10963,plain,
    ( k5_xboole_0(sK2,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_10425,c_7868])).

cnf(c_22876,plain,
    ( sK2 = X0
    | r2_hidden(sK0(sK2,k3_subset_1(sK1,sK3),X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22808,c_737,c_10963])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_475,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_736,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_476])).

cnf(c_1508,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_481])).

cnf(c_1509,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_479])).

cnf(c_1510,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_480])).

cnf(c_1517,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1509,c_1510])).

cnf(c_1522,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1508,c_1517])).

cnf(c_22904,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK0(sK2,k3_subset_1(sK1,sK3),k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_22876,c_1522])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_258,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_584,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_598,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_257,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_599,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_257])).

cnf(c_28476,plain,
    ( r2_hidden(sK0(sK2,k3_subset_1(sK1,sK3),k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22904,c_12,c_598,c_599])).

cnf(c_28491,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_28476,c_8084])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:35:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.33/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.33/1.51  
% 7.33/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.33/1.51  
% 7.33/1.51  ------  iProver source info
% 7.33/1.51  
% 7.33/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.33/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.33/1.51  git: non_committed_changes: false
% 7.33/1.51  git: last_make_outside_of_git: false
% 7.33/1.51  
% 7.33/1.51  ------ 
% 7.33/1.51  
% 7.33/1.51  ------ Input Options
% 7.33/1.51  
% 7.33/1.51  --out_options                           all
% 7.33/1.51  --tptp_safe_out                         true
% 7.33/1.51  --problem_path                          ""
% 7.33/1.51  --include_path                          ""
% 7.33/1.51  --clausifier                            res/vclausify_rel
% 7.33/1.51  --clausifier_options                    --mode clausify
% 7.33/1.51  --stdin                                 false
% 7.33/1.51  --stats_out                             all
% 7.33/1.51  
% 7.33/1.51  ------ General Options
% 7.33/1.51  
% 7.33/1.51  --fof                                   false
% 7.33/1.51  --time_out_real                         305.
% 7.33/1.51  --time_out_virtual                      -1.
% 7.33/1.51  --symbol_type_check                     false
% 7.33/1.51  --clausify_out                          false
% 7.33/1.51  --sig_cnt_out                           false
% 7.33/1.51  --trig_cnt_out                          false
% 7.33/1.51  --trig_cnt_out_tolerance                1.
% 7.33/1.51  --trig_cnt_out_sk_spl                   false
% 7.33/1.51  --abstr_cl_out                          false
% 7.33/1.51  
% 7.33/1.51  ------ Global Options
% 7.33/1.51  
% 7.33/1.51  --schedule                              default
% 7.33/1.51  --add_important_lit                     false
% 7.33/1.51  --prop_solver_per_cl                    1000
% 7.33/1.51  --min_unsat_core                        false
% 7.33/1.51  --soft_assumptions                      false
% 7.33/1.51  --soft_lemma_size                       3
% 7.33/1.51  --prop_impl_unit_size                   0
% 7.33/1.51  --prop_impl_unit                        []
% 7.33/1.51  --share_sel_clauses                     true
% 7.33/1.51  --reset_solvers                         false
% 7.33/1.51  --bc_imp_inh                            [conj_cone]
% 7.33/1.51  --conj_cone_tolerance                   3.
% 7.33/1.51  --extra_neg_conj                        none
% 7.33/1.51  --large_theory_mode                     true
% 7.33/1.51  --prolific_symb_bound                   200
% 7.33/1.51  --lt_threshold                          2000
% 7.33/1.51  --clause_weak_htbl                      true
% 7.33/1.51  --gc_record_bc_elim                     false
% 7.33/1.51  
% 7.33/1.51  ------ Preprocessing Options
% 7.33/1.51  
% 7.33/1.51  --preprocessing_flag                    true
% 7.33/1.51  --time_out_prep_mult                    0.1
% 7.33/1.51  --splitting_mode                        input
% 7.33/1.51  --splitting_grd                         true
% 7.33/1.51  --splitting_cvd                         false
% 7.33/1.51  --splitting_cvd_svl                     false
% 7.33/1.51  --splitting_nvd                         32
% 7.33/1.51  --sub_typing                            true
% 7.33/1.51  --prep_gs_sim                           true
% 7.33/1.51  --prep_unflatten                        true
% 7.33/1.51  --prep_res_sim                          true
% 7.33/1.51  --prep_upred                            true
% 7.33/1.51  --prep_sem_filter                       exhaustive
% 7.33/1.51  --prep_sem_filter_out                   false
% 7.33/1.51  --pred_elim                             true
% 7.33/1.51  --res_sim_input                         true
% 7.33/1.51  --eq_ax_congr_red                       true
% 7.33/1.51  --pure_diseq_elim                       true
% 7.33/1.51  --brand_transform                       false
% 7.33/1.51  --non_eq_to_eq                          false
% 7.33/1.51  --prep_def_merge                        true
% 7.33/1.51  --prep_def_merge_prop_impl              false
% 7.33/1.51  --prep_def_merge_mbd                    true
% 7.33/1.51  --prep_def_merge_tr_red                 false
% 7.33/1.51  --prep_def_merge_tr_cl                  false
% 7.33/1.51  --smt_preprocessing                     true
% 7.33/1.51  --smt_ac_axioms                         fast
% 7.33/1.51  --preprocessed_out                      false
% 7.33/1.51  --preprocessed_stats                    false
% 7.33/1.51  
% 7.33/1.51  ------ Abstraction refinement Options
% 7.33/1.51  
% 7.33/1.51  --abstr_ref                             []
% 7.33/1.51  --abstr_ref_prep                        false
% 7.33/1.51  --abstr_ref_until_sat                   false
% 7.33/1.51  --abstr_ref_sig_restrict                funpre
% 7.33/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.33/1.51  --abstr_ref_under                       []
% 7.33/1.51  
% 7.33/1.51  ------ SAT Options
% 7.33/1.51  
% 7.33/1.51  --sat_mode                              false
% 7.33/1.51  --sat_fm_restart_options                ""
% 7.33/1.51  --sat_gr_def                            false
% 7.33/1.51  --sat_epr_types                         true
% 7.33/1.51  --sat_non_cyclic_types                  false
% 7.33/1.51  --sat_finite_models                     false
% 7.33/1.51  --sat_fm_lemmas                         false
% 7.33/1.51  --sat_fm_prep                           false
% 7.33/1.51  --sat_fm_uc_incr                        true
% 7.33/1.51  --sat_out_model                         small
% 7.33/1.51  --sat_out_clauses                       false
% 7.33/1.51  
% 7.33/1.51  ------ QBF Options
% 7.33/1.51  
% 7.33/1.51  --qbf_mode                              false
% 7.33/1.51  --qbf_elim_univ                         false
% 7.33/1.51  --qbf_dom_inst                          none
% 7.33/1.51  --qbf_dom_pre_inst                      false
% 7.33/1.51  --qbf_sk_in                             false
% 7.33/1.51  --qbf_pred_elim                         true
% 7.33/1.51  --qbf_split                             512
% 7.33/1.51  
% 7.33/1.51  ------ BMC1 Options
% 7.33/1.51  
% 7.33/1.51  --bmc1_incremental                      false
% 7.33/1.51  --bmc1_axioms                           reachable_all
% 7.33/1.51  --bmc1_min_bound                        0
% 7.33/1.51  --bmc1_max_bound                        -1
% 7.33/1.51  --bmc1_max_bound_default                -1
% 7.33/1.51  --bmc1_symbol_reachability              true
% 7.33/1.51  --bmc1_property_lemmas                  false
% 7.33/1.51  --bmc1_k_induction                      false
% 7.33/1.51  --bmc1_non_equiv_states                 false
% 7.33/1.51  --bmc1_deadlock                         false
% 7.33/1.51  --bmc1_ucm                              false
% 7.33/1.51  --bmc1_add_unsat_core                   none
% 7.33/1.51  --bmc1_unsat_core_children              false
% 7.33/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.33/1.51  --bmc1_out_stat                         full
% 7.33/1.51  --bmc1_ground_init                      false
% 7.33/1.51  --bmc1_pre_inst_next_state              false
% 7.33/1.51  --bmc1_pre_inst_state                   false
% 7.33/1.51  --bmc1_pre_inst_reach_state             false
% 7.33/1.51  --bmc1_out_unsat_core                   false
% 7.33/1.51  --bmc1_aig_witness_out                  false
% 7.33/1.51  --bmc1_verbose                          false
% 7.33/1.51  --bmc1_dump_clauses_tptp                false
% 7.33/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.33/1.51  --bmc1_dump_file                        -
% 7.33/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.33/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.33/1.51  --bmc1_ucm_extend_mode                  1
% 7.33/1.51  --bmc1_ucm_init_mode                    2
% 7.33/1.51  --bmc1_ucm_cone_mode                    none
% 7.33/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.33/1.51  --bmc1_ucm_relax_model                  4
% 7.33/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.33/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.33/1.51  --bmc1_ucm_layered_model                none
% 7.33/1.51  --bmc1_ucm_max_lemma_size               10
% 7.33/1.51  
% 7.33/1.51  ------ AIG Options
% 7.33/1.51  
% 7.33/1.51  --aig_mode                              false
% 7.33/1.51  
% 7.33/1.51  ------ Instantiation Options
% 7.33/1.51  
% 7.33/1.51  --instantiation_flag                    true
% 7.33/1.51  --inst_sos_flag                         false
% 7.33/1.51  --inst_sos_phase                        true
% 7.33/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.33/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.33/1.51  --inst_lit_sel_side                     num_symb
% 7.33/1.51  --inst_solver_per_active                1400
% 7.33/1.51  --inst_solver_calls_frac                1.
% 7.33/1.51  --inst_passive_queue_type               priority_queues
% 7.33/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.33/1.51  --inst_passive_queues_freq              [25;2]
% 7.33/1.51  --inst_dismatching                      true
% 7.33/1.51  --inst_eager_unprocessed_to_passive     true
% 7.33/1.51  --inst_prop_sim_given                   true
% 7.33/1.51  --inst_prop_sim_new                     false
% 7.33/1.51  --inst_subs_new                         false
% 7.33/1.51  --inst_eq_res_simp                      false
% 7.33/1.51  --inst_subs_given                       false
% 7.33/1.51  --inst_orphan_elimination               true
% 7.33/1.51  --inst_learning_loop_flag               true
% 7.33/1.51  --inst_learning_start                   3000
% 7.33/1.51  --inst_learning_factor                  2
% 7.33/1.51  --inst_start_prop_sim_after_learn       3
% 7.33/1.51  --inst_sel_renew                        solver
% 7.33/1.51  --inst_lit_activity_flag                true
% 7.33/1.51  --inst_restr_to_given                   false
% 7.33/1.51  --inst_activity_threshold               500
% 7.33/1.51  --inst_out_proof                        true
% 7.33/1.51  
% 7.33/1.51  ------ Resolution Options
% 7.33/1.51  
% 7.33/1.51  --resolution_flag                       true
% 7.33/1.51  --res_lit_sel                           adaptive
% 7.33/1.51  --res_lit_sel_side                      none
% 7.33/1.51  --res_ordering                          kbo
% 7.33/1.51  --res_to_prop_solver                    active
% 7.33/1.51  --res_prop_simpl_new                    false
% 7.33/1.51  --res_prop_simpl_given                  true
% 7.33/1.51  --res_passive_queue_type                priority_queues
% 7.33/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.33/1.51  --res_passive_queues_freq               [15;5]
% 7.33/1.51  --res_forward_subs                      full
% 7.33/1.51  --res_backward_subs                     full
% 7.33/1.51  --res_forward_subs_resolution           true
% 7.33/1.51  --res_backward_subs_resolution          true
% 7.33/1.51  --res_orphan_elimination                true
% 7.33/1.51  --res_time_limit                        2.
% 7.33/1.51  --res_out_proof                         true
% 7.33/1.51  
% 7.33/1.51  ------ Superposition Options
% 7.33/1.51  
% 7.33/1.51  --superposition_flag                    true
% 7.33/1.51  --sup_passive_queue_type                priority_queues
% 7.33/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.33/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.33/1.51  --demod_completeness_check              fast
% 7.33/1.51  --demod_use_ground                      true
% 7.33/1.51  --sup_to_prop_solver                    passive
% 7.33/1.51  --sup_prop_simpl_new                    true
% 7.33/1.51  --sup_prop_simpl_given                  true
% 7.33/1.51  --sup_fun_splitting                     false
% 7.33/1.51  --sup_smt_interval                      50000
% 7.33/1.51  
% 7.33/1.51  ------ Superposition Simplification Setup
% 7.33/1.51  
% 7.33/1.51  --sup_indices_passive                   []
% 7.33/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.33/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.51  --sup_full_bw                           [BwDemod]
% 7.33/1.51  --sup_immed_triv                        [TrivRules]
% 7.33/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.51  --sup_immed_bw_main                     []
% 7.33/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.33/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.33/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.33/1.51  
% 7.33/1.51  ------ Combination Options
% 7.33/1.51  
% 7.33/1.51  --comb_res_mult                         3
% 7.33/1.51  --comb_sup_mult                         2
% 7.33/1.51  --comb_inst_mult                        10
% 7.33/1.51  
% 7.33/1.51  ------ Debug Options
% 7.33/1.51  
% 7.33/1.51  --dbg_backtrace                         false
% 7.33/1.51  --dbg_dump_prop_clauses                 false
% 7.33/1.51  --dbg_dump_prop_clauses_file            -
% 7.33/1.51  --dbg_out_stat                          false
% 7.33/1.51  ------ Parsing...
% 7.33/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.33/1.51  
% 7.33/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.33/1.51  
% 7.33/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.33/1.51  
% 7.33/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.33/1.51  ------ Proving...
% 7.33/1.51  ------ Problem Properties 
% 7.33/1.51  
% 7.33/1.51  
% 7.33/1.51  clauses                                 14
% 7.33/1.51  conjectures                             3
% 7.33/1.51  EPR                                     5
% 7.33/1.51  Horn                                    10
% 7.33/1.51  unary                                   5
% 7.33/1.51  binary                                  4
% 7.33/1.51  lits                                    29
% 7.33/1.51  lits eq                                 8
% 7.33/1.51  fd_pure                                 0
% 7.33/1.51  fd_pseudo                               0
% 7.33/1.51  fd_cond                                 0
% 7.33/1.51  fd_pseudo_cond                          4
% 7.33/1.51  AC symbols                              0
% 7.33/1.51  
% 7.33/1.51  ------ Schedule dynamic 5 is on 
% 7.33/1.51  
% 7.33/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.33/1.51  
% 7.33/1.51  
% 7.33/1.51  ------ 
% 7.33/1.51  Current options:
% 7.33/1.51  ------ 
% 7.33/1.51  
% 7.33/1.51  ------ Input Options
% 7.33/1.51  
% 7.33/1.51  --out_options                           all
% 7.33/1.51  --tptp_safe_out                         true
% 7.33/1.51  --problem_path                          ""
% 7.33/1.51  --include_path                          ""
% 7.33/1.51  --clausifier                            res/vclausify_rel
% 7.33/1.51  --clausifier_options                    --mode clausify
% 7.33/1.51  --stdin                                 false
% 7.33/1.51  --stats_out                             all
% 7.33/1.51  
% 7.33/1.51  ------ General Options
% 7.33/1.51  
% 7.33/1.51  --fof                                   false
% 7.33/1.51  --time_out_real                         305.
% 7.33/1.51  --time_out_virtual                      -1.
% 7.33/1.51  --symbol_type_check                     false
% 7.33/1.51  --clausify_out                          false
% 7.33/1.51  --sig_cnt_out                           false
% 7.33/1.51  --trig_cnt_out                          false
% 7.33/1.51  --trig_cnt_out_tolerance                1.
% 7.33/1.51  --trig_cnt_out_sk_spl                   false
% 7.33/1.51  --abstr_cl_out                          false
% 7.33/1.51  
% 7.33/1.51  ------ Global Options
% 7.33/1.51  
% 7.33/1.51  --schedule                              default
% 7.33/1.51  --add_important_lit                     false
% 7.33/1.51  --prop_solver_per_cl                    1000
% 7.33/1.51  --min_unsat_core                        false
% 7.33/1.51  --soft_assumptions                      false
% 7.33/1.51  --soft_lemma_size                       3
% 7.33/1.51  --prop_impl_unit_size                   0
% 7.33/1.51  --prop_impl_unit                        []
% 7.33/1.51  --share_sel_clauses                     true
% 7.33/1.51  --reset_solvers                         false
% 7.33/1.51  --bc_imp_inh                            [conj_cone]
% 7.33/1.51  --conj_cone_tolerance                   3.
% 7.33/1.51  --extra_neg_conj                        none
% 7.33/1.51  --large_theory_mode                     true
% 7.33/1.51  --prolific_symb_bound                   200
% 7.33/1.51  --lt_threshold                          2000
% 7.33/1.51  --clause_weak_htbl                      true
% 7.33/1.51  --gc_record_bc_elim                     false
% 7.33/1.51  
% 7.33/1.51  ------ Preprocessing Options
% 7.33/1.51  
% 7.33/1.51  --preprocessing_flag                    true
% 7.33/1.51  --time_out_prep_mult                    0.1
% 7.33/1.51  --splitting_mode                        input
% 7.33/1.51  --splitting_grd                         true
% 7.33/1.51  --splitting_cvd                         false
% 7.33/1.51  --splitting_cvd_svl                     false
% 7.33/1.51  --splitting_nvd                         32
% 7.33/1.51  --sub_typing                            true
% 7.33/1.51  --prep_gs_sim                           true
% 7.33/1.51  --prep_unflatten                        true
% 7.33/1.51  --prep_res_sim                          true
% 7.33/1.51  --prep_upred                            true
% 7.33/1.51  --prep_sem_filter                       exhaustive
% 7.33/1.51  --prep_sem_filter_out                   false
% 7.33/1.51  --pred_elim                             true
% 7.33/1.51  --res_sim_input                         true
% 7.33/1.51  --eq_ax_congr_red                       true
% 7.33/1.51  --pure_diseq_elim                       true
% 7.33/1.51  --brand_transform                       false
% 7.33/1.51  --non_eq_to_eq                          false
% 7.33/1.51  --prep_def_merge                        true
% 7.33/1.51  --prep_def_merge_prop_impl              false
% 7.33/1.51  --prep_def_merge_mbd                    true
% 7.33/1.51  --prep_def_merge_tr_red                 false
% 7.33/1.51  --prep_def_merge_tr_cl                  false
% 7.33/1.51  --smt_preprocessing                     true
% 7.33/1.51  --smt_ac_axioms                         fast
% 7.33/1.51  --preprocessed_out                      false
% 7.33/1.51  --preprocessed_stats                    false
% 7.33/1.51  
% 7.33/1.51  ------ Abstraction refinement Options
% 7.33/1.51  
% 7.33/1.51  --abstr_ref                             []
% 7.33/1.51  --abstr_ref_prep                        false
% 7.33/1.51  --abstr_ref_until_sat                   false
% 7.33/1.51  --abstr_ref_sig_restrict                funpre
% 7.33/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.33/1.51  --abstr_ref_under                       []
% 7.33/1.51  
% 7.33/1.51  ------ SAT Options
% 7.33/1.51  
% 7.33/1.51  --sat_mode                              false
% 7.33/1.51  --sat_fm_restart_options                ""
% 7.33/1.51  --sat_gr_def                            false
% 7.33/1.51  --sat_epr_types                         true
% 7.33/1.51  --sat_non_cyclic_types                  false
% 7.33/1.51  --sat_finite_models                     false
% 7.33/1.51  --sat_fm_lemmas                         false
% 7.33/1.51  --sat_fm_prep                           false
% 7.33/1.51  --sat_fm_uc_incr                        true
% 7.33/1.51  --sat_out_model                         small
% 7.33/1.51  --sat_out_clauses                       false
% 7.33/1.51  
% 7.33/1.51  ------ QBF Options
% 7.33/1.51  
% 7.33/1.51  --qbf_mode                              false
% 7.33/1.51  --qbf_elim_univ                         false
% 7.33/1.51  --qbf_dom_inst                          none
% 7.33/1.51  --qbf_dom_pre_inst                      false
% 7.33/1.51  --qbf_sk_in                             false
% 7.33/1.51  --qbf_pred_elim                         true
% 7.33/1.51  --qbf_split                             512
% 7.33/1.51  
% 7.33/1.51  ------ BMC1 Options
% 7.33/1.51  
% 7.33/1.51  --bmc1_incremental                      false
% 7.33/1.51  --bmc1_axioms                           reachable_all
% 7.33/1.51  --bmc1_min_bound                        0
% 7.33/1.51  --bmc1_max_bound                        -1
% 7.33/1.51  --bmc1_max_bound_default                -1
% 7.33/1.51  --bmc1_symbol_reachability              true
% 7.33/1.51  --bmc1_property_lemmas                  false
% 7.33/1.51  --bmc1_k_induction                      false
% 7.33/1.51  --bmc1_non_equiv_states                 false
% 7.33/1.51  --bmc1_deadlock                         false
% 7.33/1.51  --bmc1_ucm                              false
% 7.33/1.51  --bmc1_add_unsat_core                   none
% 7.33/1.51  --bmc1_unsat_core_children              false
% 7.33/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.33/1.51  --bmc1_out_stat                         full
% 7.33/1.51  --bmc1_ground_init                      false
% 7.33/1.51  --bmc1_pre_inst_next_state              false
% 7.33/1.51  --bmc1_pre_inst_state                   false
% 7.33/1.51  --bmc1_pre_inst_reach_state             false
% 7.33/1.51  --bmc1_out_unsat_core                   false
% 7.33/1.51  --bmc1_aig_witness_out                  false
% 7.33/1.51  --bmc1_verbose                          false
% 7.33/1.51  --bmc1_dump_clauses_tptp                false
% 7.33/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.33/1.51  --bmc1_dump_file                        -
% 7.33/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.33/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.33/1.51  --bmc1_ucm_extend_mode                  1
% 7.33/1.51  --bmc1_ucm_init_mode                    2
% 7.33/1.51  --bmc1_ucm_cone_mode                    none
% 7.33/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.33/1.51  --bmc1_ucm_relax_model                  4
% 7.33/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.33/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.33/1.51  --bmc1_ucm_layered_model                none
% 7.33/1.51  --bmc1_ucm_max_lemma_size               10
% 7.33/1.51  
% 7.33/1.51  ------ AIG Options
% 7.33/1.51  
% 7.33/1.51  --aig_mode                              false
% 7.33/1.51  
% 7.33/1.51  ------ Instantiation Options
% 7.33/1.51  
% 7.33/1.51  --instantiation_flag                    true
% 7.33/1.51  --inst_sos_flag                         false
% 7.33/1.51  --inst_sos_phase                        true
% 7.33/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.33/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.33/1.51  --inst_lit_sel_side                     none
% 7.33/1.51  --inst_solver_per_active                1400
% 7.33/1.51  --inst_solver_calls_frac                1.
% 7.33/1.51  --inst_passive_queue_type               priority_queues
% 7.33/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.33/1.51  --inst_passive_queues_freq              [25;2]
% 7.33/1.51  --inst_dismatching                      true
% 7.33/1.51  --inst_eager_unprocessed_to_passive     true
% 7.33/1.51  --inst_prop_sim_given                   true
% 7.33/1.51  --inst_prop_sim_new                     false
% 7.33/1.51  --inst_subs_new                         false
% 7.33/1.51  --inst_eq_res_simp                      false
% 7.33/1.51  --inst_subs_given                       false
% 7.33/1.51  --inst_orphan_elimination               true
% 7.33/1.51  --inst_learning_loop_flag               true
% 7.33/1.51  --inst_learning_start                   3000
% 7.33/1.51  --inst_learning_factor                  2
% 7.33/1.51  --inst_start_prop_sim_after_learn       3
% 7.33/1.51  --inst_sel_renew                        solver
% 7.33/1.51  --inst_lit_activity_flag                true
% 7.33/1.51  --inst_restr_to_given                   false
% 7.33/1.51  --inst_activity_threshold               500
% 7.33/1.51  --inst_out_proof                        true
% 7.33/1.51  
% 7.33/1.51  ------ Resolution Options
% 7.33/1.51  
% 7.33/1.51  --resolution_flag                       false
% 7.33/1.51  --res_lit_sel                           adaptive
% 7.33/1.51  --res_lit_sel_side                      none
% 7.33/1.51  --res_ordering                          kbo
% 7.33/1.51  --res_to_prop_solver                    active
% 7.33/1.51  --res_prop_simpl_new                    false
% 7.33/1.51  --res_prop_simpl_given                  true
% 7.33/1.51  --res_passive_queue_type                priority_queues
% 7.33/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.33/1.51  --res_passive_queues_freq               [15;5]
% 7.33/1.51  --res_forward_subs                      full
% 7.33/1.51  --res_backward_subs                     full
% 7.33/1.51  --res_forward_subs_resolution           true
% 7.33/1.51  --res_backward_subs_resolution          true
% 7.33/1.51  --res_orphan_elimination                true
% 7.33/1.51  --res_time_limit                        2.
% 7.33/1.51  --res_out_proof                         true
% 7.33/1.51  
% 7.33/1.51  ------ Superposition Options
% 7.33/1.51  
% 7.33/1.51  --superposition_flag                    true
% 7.33/1.51  --sup_passive_queue_type                priority_queues
% 7.33/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.33/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.33/1.51  --demod_completeness_check              fast
% 7.33/1.51  --demod_use_ground                      true
% 7.33/1.51  --sup_to_prop_solver                    passive
% 7.33/1.51  --sup_prop_simpl_new                    true
% 7.33/1.51  --sup_prop_simpl_given                  true
% 7.33/1.51  --sup_fun_splitting                     false
% 7.33/1.51  --sup_smt_interval                      50000
% 7.33/1.51  
% 7.33/1.51  ------ Superposition Simplification Setup
% 7.33/1.51  
% 7.33/1.51  --sup_indices_passive                   []
% 7.33/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.33/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.51  --sup_full_bw                           [BwDemod]
% 7.33/1.51  --sup_immed_triv                        [TrivRules]
% 7.33/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.51  --sup_immed_bw_main                     []
% 7.33/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.33/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.33/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.33/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.33/1.51  
% 7.33/1.51  ------ Combination Options
% 7.33/1.51  
% 7.33/1.51  --comb_res_mult                         3
% 7.33/1.51  --comb_sup_mult                         2
% 7.33/1.51  --comb_inst_mult                        10
% 7.33/1.51  
% 7.33/1.51  ------ Debug Options
% 7.33/1.51  
% 7.33/1.51  --dbg_backtrace                         false
% 7.33/1.51  --dbg_dump_prop_clauses                 false
% 7.33/1.51  --dbg_dump_prop_clauses_file            -
% 7.33/1.51  --dbg_out_stat                          false
% 7.33/1.51  
% 7.33/1.51  
% 7.33/1.51  
% 7.33/1.51  
% 7.33/1.51  ------ Proving...
% 7.33/1.51  
% 7.33/1.51  
% 7.33/1.51  % SZS status Theorem for theBenchmark.p
% 7.33/1.51  
% 7.33/1.51   Resolution empty clause
% 7.33/1.51  
% 7.33/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.33/1.51  
% 7.33/1.51  fof(f6,axiom,(
% 7.33/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.33/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.51  
% 7.33/1.51  fof(f10,plain,(
% 7.33/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.33/1.51    inference(ennf_transformation,[],[f6])).
% 7.33/1.51  
% 7.33/1.51  fof(f34,plain,(
% 7.33/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.33/1.51    inference(cnf_transformation,[],[f10])).
% 7.33/1.51  
% 7.33/1.51  fof(f3,axiom,(
% 7.33/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.33/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.51  
% 7.33/1.51  fof(f31,plain,(
% 7.33/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.33/1.51    inference(cnf_transformation,[],[f3])).
% 7.33/1.51  
% 7.33/1.51  fof(f45,plain,(
% 7.33/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.33/1.51    inference(definition_unfolding,[],[f34,f31])).
% 7.33/1.51  
% 7.33/1.51  fof(f7,conjecture,(
% 7.33/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 7.33/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.51  
% 7.33/1.51  fof(f8,negated_conjecture,(
% 7.33/1.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 7.33/1.51    inference(negated_conjecture,[],[f7])).
% 7.33/1.51  
% 7.33/1.51  fof(f11,plain,(
% 7.33/1.51    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.33/1.51    inference(ennf_transformation,[],[f8])).
% 7.33/1.51  
% 7.33/1.51  fof(f12,plain,(
% 7.33/1.51    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.33/1.51    inference(flattening,[],[f11])).
% 7.33/1.51  
% 7.33/1.51  fof(f20,plain,(
% 7.33/1.51    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 7.33/1.51    introduced(choice_axiom,[])).
% 7.33/1.51  
% 7.33/1.51  fof(f21,plain,(
% 7.33/1.51    k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.33/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f12,f20])).
% 7.33/1.51  
% 7.33/1.51  fof(f35,plain,(
% 7.33/1.51    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.33/1.51    inference(cnf_transformation,[],[f21])).
% 7.33/1.51  
% 7.33/1.51  fof(f1,axiom,(
% 7.33/1.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.33/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.51  
% 7.33/1.51  fof(f13,plain,(
% 7.33/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.33/1.51    inference(nnf_transformation,[],[f1])).
% 7.33/1.51  
% 7.33/1.51  fof(f14,plain,(
% 7.33/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.33/1.51    inference(flattening,[],[f13])).
% 7.33/1.51  
% 7.33/1.51  fof(f15,plain,(
% 7.33/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.33/1.51    inference(rectify,[],[f14])).
% 7.33/1.51  
% 7.33/1.51  fof(f16,plain,(
% 7.33/1.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.33/1.51    introduced(choice_axiom,[])).
% 7.33/1.51  
% 7.33/1.51  fof(f17,plain,(
% 7.33/1.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.33/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 7.33/1.51  
% 7.33/1.51  fof(f25,plain,(
% 7.33/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.33/1.51    inference(cnf_transformation,[],[f17])).
% 7.33/1.51  
% 7.33/1.51  fof(f41,plain,(
% 7.33/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.33/1.51    inference(definition_unfolding,[],[f25,f31])).
% 7.33/1.51  
% 7.33/1.51  fof(f36,plain,(
% 7.33/1.51    r1_tarski(sK2,sK3)),
% 7.33/1.51    inference(cnf_transformation,[],[f21])).
% 7.33/1.51  
% 7.33/1.51  fof(f4,axiom,(
% 7.33/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.33/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.51  
% 7.33/1.51  fof(f9,plain,(
% 7.33/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.33/1.51    inference(ennf_transformation,[],[f4])).
% 7.33/1.51  
% 7.33/1.51  fof(f32,plain,(
% 7.33/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.33/1.51    inference(cnf_transformation,[],[f9])).
% 7.33/1.51  
% 7.33/1.51  fof(f24,plain,(
% 7.33/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.33/1.51    inference(cnf_transformation,[],[f17])).
% 7.33/1.51  
% 7.33/1.51  fof(f42,plain,(
% 7.33/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.33/1.51    inference(definition_unfolding,[],[f24,f31])).
% 7.33/1.51  
% 7.33/1.51  fof(f46,plain,(
% 7.33/1.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.33/1.51    inference(equality_resolution,[],[f42])).
% 7.33/1.51  
% 7.33/1.51  fof(f23,plain,(
% 7.33/1.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.33/1.51    inference(cnf_transformation,[],[f17])).
% 7.33/1.51  
% 7.33/1.51  fof(f43,plain,(
% 7.33/1.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.33/1.51    inference(definition_unfolding,[],[f23,f31])).
% 7.33/1.51  
% 7.33/1.51  fof(f47,plain,(
% 7.33/1.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.33/1.51    inference(equality_resolution,[],[f43])).
% 7.33/1.51  
% 7.33/1.51  fof(f37,plain,(
% 7.33/1.51    r1_tarski(sK2,k3_subset_1(sK1,sK3))),
% 7.33/1.51    inference(cnf_transformation,[],[f21])).
% 7.33/1.51  
% 7.33/1.51  fof(f22,plain,(
% 7.33/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.33/1.51    inference(cnf_transformation,[],[f17])).
% 7.33/1.51  
% 7.33/1.51  fof(f44,plain,(
% 7.33/1.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.33/1.51    inference(definition_unfolding,[],[f22,f31])).
% 7.33/1.51  
% 7.33/1.51  fof(f48,plain,(
% 7.33/1.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.33/1.51    inference(equality_resolution,[],[f44])).
% 7.33/1.51  
% 7.33/1.51  fof(f26,plain,(
% 7.33/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.33/1.51    inference(cnf_transformation,[],[f17])).
% 7.33/1.51  
% 7.33/1.51  fof(f40,plain,(
% 7.33/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.33/1.51    inference(definition_unfolding,[],[f26,f31])).
% 7.33/1.51  
% 7.33/1.51  fof(f2,axiom,(
% 7.33/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.33/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.51  
% 7.33/1.51  fof(f18,plain,(
% 7.33/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.33/1.51    inference(nnf_transformation,[],[f2])).
% 7.33/1.51  
% 7.33/1.51  fof(f19,plain,(
% 7.33/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.33/1.51    inference(flattening,[],[f18])).
% 7.33/1.51  
% 7.33/1.51  fof(f28,plain,(
% 7.33/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.33/1.51    inference(cnf_transformation,[],[f19])).
% 7.33/1.51  
% 7.33/1.51  fof(f50,plain,(
% 7.33/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.33/1.51    inference(equality_resolution,[],[f28])).
% 7.33/1.51  
% 7.33/1.51  fof(f5,axiom,(
% 7.33/1.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.33/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.51  
% 7.33/1.51  fof(f33,plain,(
% 7.33/1.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.33/1.51    inference(cnf_transformation,[],[f5])).
% 7.33/1.51  
% 7.33/1.51  fof(f38,plain,(
% 7.33/1.51    k1_xboole_0 != sK2),
% 7.33/1.51    inference(cnf_transformation,[],[f21])).
% 7.33/1.51  
% 7.33/1.51  cnf(c_11,plain,
% 7.33/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.33/1.51      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 7.33/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_15,negated_conjecture,
% 7.33/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.33/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_161,plain,
% 7.33/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 7.33/1.51      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 7.33/1.51      | sK3 != X1 ),
% 7.33/1.51      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_162,plain,
% 7.33/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
% 7.33/1.51      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 7.33/1.51      inference(unflattening,[status(thm)],[c_161]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_591,plain,
% 7.33/1.51      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
% 7.33/1.51      inference(equality_resolution,[status(thm)],[c_162]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_2,plain,
% 7.33/1.51      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.33/1.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.33/1.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.33/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_482,plain,
% 7.33/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 7.33/1.51      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 7.33/1.51      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.33/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_14,negated_conjecture,
% 7.33/1.51      ( r1_tarski(sK2,sK3) ),
% 7.33/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_473,plain,
% 7.33/1.51      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.33/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_9,plain,
% 7.33/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.33/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_476,plain,
% 7.33/1.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.33/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_738,plain,
% 7.33/1.51      ( k3_xboole_0(sK2,sK3) = sK2 ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_473,c_476]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_3,plain,
% 7.33/1.51      ( ~ r2_hidden(X0,X1)
% 7.33/1.51      | r2_hidden(X0,X2)
% 7.33/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.33/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_481,plain,
% 7.33/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.33/1.51      | r2_hidden(X0,X2) = iProver_top
% 7.33/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 7.33/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1062,plain,
% 7.33/1.51      ( r2_hidden(X0,k5_xboole_0(sK2,sK2)) = iProver_top
% 7.33/1.51      | r2_hidden(X0,sK3) = iProver_top
% 7.33/1.51      | r2_hidden(X0,sK2) != iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_738,c_481]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_4,plain,
% 7.33/1.51      ( ~ r2_hidden(X0,X1)
% 7.33/1.51      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 7.33/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_480,plain,
% 7.33/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.33/1.51      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 7.33/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_930,plain,
% 7.33/1.51      ( r2_hidden(X0,k3_subset_1(sK1,sK3)) != iProver_top
% 7.33/1.51      | r2_hidden(X0,sK3) != iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_591,c_480]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_13,negated_conjecture,
% 7.33/1.51      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
% 7.33/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_474,plain,
% 7.33/1.51      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 7.33/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_737,plain,
% 7.33/1.51      ( k3_xboole_0(sK2,k3_subset_1(sK1,sK3)) = sK2 ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_474,c_476]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1140,plain,
% 7.33/1.51      ( r2_hidden(X0,k3_subset_1(sK1,sK3)) = iProver_top
% 7.33/1.51      | r2_hidden(X0,k5_xboole_0(sK2,sK2)) = iProver_top
% 7.33/1.51      | r2_hidden(X0,sK2) != iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_737,c_481]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_2078,plain,
% 7.33/1.51      ( r2_hidden(X0,k5_xboole_0(sK2,sK2)) = iProver_top
% 7.33/1.51      | r2_hidden(X0,sK2) != iProver_top ),
% 7.33/1.51      inference(global_propositional_subsumption,
% 7.33/1.51                [status(thm)],
% 7.33/1.51                [c_1062,c_930,c_1140]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_5,plain,
% 7.33/1.51      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.33/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_479,plain,
% 7.33/1.51      ( r2_hidden(X0,X1) = iProver_top
% 7.33/1.51      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 7.33/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_809,plain,
% 7.33/1.51      ( r2_hidden(X0,k3_subset_1(sK1,sK3)) != iProver_top
% 7.33/1.51      | r2_hidden(X0,sK1) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_591,c_479]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1224,plain,
% 7.33/1.51      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),X0)) = X1
% 7.33/1.51      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),X1) = iProver_top
% 7.33/1.51      | r2_hidden(sK0(k3_subset_1(sK1,sK3),X0,X1),sK1) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_482,c_809]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1,plain,
% 7.33/1.51      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.33/1.51      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.33/1.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.33/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_483,plain,
% 7.33/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 7.33/1.51      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top
% 7.33/1.51      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 7.33/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_2480,plain,
% 7.33/1.51      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = X0
% 7.33/1.51      | r2_hidden(sK0(k3_subset_1(sK1,sK3),sK1,X0),X0) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_1224,c_483]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1063,plain,
% 7.33/1.51      ( r2_hidden(X0,k5_xboole_0(sK2,sK2)) != iProver_top
% 7.33/1.51      | r2_hidden(X0,sK2) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_738,c_479]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_2766,plain,
% 7.33/1.51      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(sK2,sK2)
% 7.33/1.51      | r2_hidden(sK0(k3_subset_1(sK1,sK3),sK1,k5_xboole_0(sK2,sK2)),sK2) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_2480,c_1063]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_2757,plain,
% 7.33/1.51      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 7.33/1.51      | r2_hidden(sK0(k3_subset_1(sK1,sK3),sK1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_2480,c_479]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_2758,plain,
% 7.33/1.51      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 7.33/1.51      | r2_hidden(sK0(k3_subset_1(sK1,sK3),sK1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_2480,c_480]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_6424,plain,
% 7.33/1.51      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_2757,c_2758]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_8,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f50]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_477,plain,
% 7.33/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.33/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_735,plain,
% 7.33/1.51      ( k3_xboole_0(X0,X0) = X0 ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_477,c_476]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_6452,plain,
% 7.33/1.51      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(X0,X0) ),
% 7.33/1.51      inference(light_normalisation,[status(thm)],[c_6424,c_735]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_6481,plain,
% 7.33/1.51      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(sK2,sK2) ),
% 7.33/1.51      inference(instantiation,[status(thm)],[c_6452]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_7868,plain,
% 7.33/1.51      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = k5_xboole_0(sK2,sK2) ),
% 7.33/1.51      inference(global_propositional_subsumption,[status(thm)],[c_2766,c_6481]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_7948,plain,
% 7.33/1.51      ( r2_hidden(X0,k3_subset_1(sK1,sK3)) = iProver_top
% 7.33/1.51      | r2_hidden(X0,k5_xboole_0(sK2,sK2)) != iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_7868,c_479]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1142,plain,
% 7.33/1.51      ( r2_hidden(X0,k3_subset_1(sK1,sK3)) != iProver_top
% 7.33/1.51      | r2_hidden(X0,k5_xboole_0(sK2,sK2)) != iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_737,c_480]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_8077,plain,
% 7.33/1.51      ( r2_hidden(X0,k5_xboole_0(sK2,sK2)) != iProver_top ),
% 7.33/1.51      inference(global_propositional_subsumption,[status(thm)],[c_7948,c_1142]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_8084,plain,
% 7.33/1.51      ( r2_hidden(X0,sK2) != iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_2078,c_8077]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_8644,plain,
% 7.33/1.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = sK2
% 7.33/1.51      | r2_hidden(sK0(X0,X1,sK2),X0) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_482,c_8084]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_9277,plain,
% 7.33/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = sK2
% 7.33/1.51      | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,sK2),X0) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_8644,c_479]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_9599,plain,
% 7.33/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = sK2
% 7.33/1.51      | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0,sK2),sK2) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_9277,c_483]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_10417,plain,
% 7.33/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) = sK2 ),
% 7.33/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_9599,c_8084]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_10425,plain,
% 7.33/1.51      ( k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)) = sK2 ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_591,c_10417]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1019,plain,
% 7.33/1.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = X3
% 7.33/1.51      | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,X3),X3) = iProver_top
% 7.33/1.51      | r2_hidden(sK0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2,X3),X0) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_482,c_479]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_21972,plain,
% 7.33/1.51      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)),k3_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)),X0)) = X1
% 7.33/1.51      | r2_hidden(sK0(k5_xboole_0(k3_subset_1(sK1,sK3),k3_xboole_0(k3_subset_1(sK1,sK3),sK1)),X0,X1),k3_subset_1(sK1,sK3)) = iProver_top
% 7.33/1.51      | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_10425,c_1019]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_22207,plain,
% 7.33/1.51      ( k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = X1
% 7.33/1.51      | r2_hidden(sK0(sK2,X0,X1),X1) = iProver_top
% 7.33/1.51      | r2_hidden(sK0(sK2,X0,X1),k3_subset_1(sK1,sK3)) = iProver_top ),
% 7.33/1.51      inference(light_normalisation,[status(thm)],[c_21972,c_10425]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_22808,plain,
% 7.33/1.51      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k3_subset_1(sK1,sK3))) = X0
% 7.33/1.51      | r2_hidden(sK0(sK2,k3_subset_1(sK1,sK3),X0),X0) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_22207,c_483]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_10963,plain,
% 7.33/1.51      ( k5_xboole_0(sK2,sK2) = sK2 ),
% 7.33/1.51      inference(demodulation,[status(thm)],[c_10425,c_7868]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_22876,plain,
% 7.33/1.51      ( sK2 = X0
% 7.33/1.51      | r2_hidden(sK0(sK2,k3_subset_1(sK1,sK3),X0),X0) = iProver_top ),
% 7.33/1.51      inference(light_normalisation,[status(thm)],[c_22808,c_737,c_10963]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_10,plain,
% 7.33/1.51      ( r1_tarski(k1_xboole_0,X0) ),
% 7.33/1.51      inference(cnf_transformation,[],[f33]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_475,plain,
% 7.33/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.33/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_736,plain,
% 7.33/1.51      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_475,c_476]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1508,plain,
% 7.33/1.51      ( r2_hidden(X0,X1) = iProver_top
% 7.33/1.51      | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = iProver_top
% 7.33/1.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_736,c_481]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1509,plain,
% 7.33/1.51      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.33/1.51      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_736,c_479]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1510,plain,
% 7.33/1.51      ( r2_hidden(X0,X1) != iProver_top
% 7.33/1.51      | r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_736,c_480]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1517,plain,
% 7.33/1.51      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.33/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_1509,c_1510]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_1522,plain,
% 7.33/1.51      ( r2_hidden(X0,X1) = iProver_top
% 7.33/1.51      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.33/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_1508,c_1517]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_22904,plain,
% 7.33/1.51      ( sK2 = k1_xboole_0
% 7.33/1.51      | r2_hidden(sK0(sK2,k3_subset_1(sK1,sK3),k1_xboole_0),X0) = iProver_top ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_22876,c_1522]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_12,negated_conjecture,
% 7.33/1.51      ( k1_xboole_0 != sK2 ),
% 7.33/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_258,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_584,plain,
% 7.33/1.51      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 7.33/1.51      inference(instantiation,[status(thm)],[c_258]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_598,plain,
% 7.33/1.51      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 7.33/1.51      inference(instantiation,[status(thm)],[c_584]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_257,plain,( X0 = X0 ),theory(equality) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_599,plain,
% 7.33/1.51      ( k1_xboole_0 = k1_xboole_0 ),
% 7.33/1.51      inference(instantiation,[status(thm)],[c_257]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_28476,plain,
% 7.33/1.51      ( r2_hidden(sK0(sK2,k3_subset_1(sK1,sK3),k1_xboole_0),X0) = iProver_top ),
% 7.33/1.51      inference(global_propositional_subsumption,
% 7.33/1.51                [status(thm)],
% 7.33/1.51                [c_22904,c_12,c_598,c_599]) ).
% 7.33/1.51  
% 7.33/1.51  cnf(c_28491,plain,
% 7.33/1.51      ( $false ),
% 7.33/1.51      inference(superposition,[status(thm)],[c_28476,c_8084]) ).
% 7.33/1.51  
% 7.33/1.51  
% 7.33/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.33/1.51  
% 7.33/1.51  ------                               Statistics
% 7.33/1.51  
% 7.33/1.51  ------ General
% 7.33/1.51  
% 7.33/1.51  abstr_ref_over_cycles:                  0
% 7.33/1.51  abstr_ref_under_cycles:                 0
% 7.33/1.51  gc_basic_clause_elim:                   0
% 7.33/1.51  forced_gc_time:                         0
% 7.33/1.51  parsing_time:                           0.01
% 7.33/1.51  unif_index_cands_time:                  0.
% 7.33/1.51  unif_index_add_time:                    0.
% 7.33/1.51  orderings_time:                         0.
% 7.33/1.51  out_proof_time:                         0.009
% 7.33/1.51  total_time:                             0.848
% 7.33/1.51  num_of_symbols:                         43
% 7.33/1.51  num_of_terms:                           30384
% 7.33/1.51  
% 7.33/1.51  ------ Preprocessing
% 7.33/1.51  
% 7.33/1.51  num_of_splits:                          0
% 7.33/1.51  num_of_split_atoms:                     0
% 7.33/1.51  num_of_reused_defs:                     0
% 7.33/1.51  num_eq_ax_congr_red:                    16
% 7.33/1.51  num_of_sem_filtered_clauses:            1
% 7.33/1.51  num_of_subtypes:                        0
% 7.33/1.51  monotx_restored_types:                  0
% 7.33/1.51  sat_num_of_epr_types:                   0
% 7.33/1.51  sat_num_of_non_cyclic_types:            0
% 7.33/1.51  sat_guarded_non_collapsed_types:        0
% 7.33/1.51  num_pure_diseq_elim:                    0
% 7.33/1.51  simp_replaced_by:                       0
% 7.33/1.51  res_preprocessed:                       74
% 7.33/1.51  prep_upred:                             0
% 7.33/1.51  prep_unflattend:                        1
% 7.33/1.51  smt_new_axioms:                         0
% 7.33/1.51  pred_elim_cands:                        2
% 7.33/1.51  pred_elim:                              1
% 7.33/1.51  pred_elim_cl:                           1
% 7.33/1.51  pred_elim_cycles:                       3
% 7.33/1.51  merged_defs:                            0
% 7.33/1.51  merged_defs_ncl:                        0
% 7.33/1.51  bin_hyper_res:                          0
% 7.33/1.51  prep_cycles:                            4
% 7.33/1.51  pred_elim_time:                         0.001
% 7.33/1.51  splitting_time:                         0.
% 7.33/1.51  sem_filter_time:                        0.
% 7.33/1.51  monotx_time:                            0.001
% 7.33/1.51  subtype_inf_time:                       0.
% 7.33/1.51  
% 7.33/1.51  ------ Problem properties
% 7.33/1.51  
% 7.33/1.51  clauses:                                14
% 7.33/1.51  conjectures:                            3
% 7.33/1.51  epr:                                    5
% 7.33/1.51  horn:                                   10
% 7.33/1.51  ground:                                 3
% 7.33/1.51  unary:                                  5
% 7.33/1.51  binary:                                 4
% 7.33/1.51  lits:                                   29
% 7.33/1.51  lits_eq:                                8
% 7.33/1.51  fd_pure:                                0
% 7.33/1.51  fd_pseudo:                              0
% 7.33/1.51  fd_cond:                                0
% 7.33/1.51  fd_pseudo_cond:                         4
% 7.33/1.51  ac_symbols:                             0
% 7.33/1.51  
% 7.33/1.51  ------ Propositional Solver
% 7.33/1.51  
% 7.33/1.51  prop_solver_calls:                      32
% 7.33/1.51  prop_fast_solver_calls:                 843
% 7.33/1.51  smt_solver_calls:                       0
% 7.33/1.51  smt_fast_solver_calls:                  0
% 7.33/1.51  prop_num_of_clauses:                    9865
% 7.33/1.51  prop_preprocess_simplified:             17224
% 7.33/1.51  prop_fo_subsumed:                       13
% 7.33/1.51  prop_solver_time:                       0.
% 7.33/1.51  smt_solver_time:                        0.
% 7.33/1.51  smt_fast_solver_time:                   0.
% 7.33/1.51  prop_fast_solver_time:                  0.
% 7.33/1.51  prop_unsat_core_time:                   0.
% 7.33/1.51  
% 7.33/1.51  ------ QBF
% 7.33/1.51  
% 7.33/1.51  qbf_q_res:                              0
% 7.33/1.51  qbf_num_tautologies:                    0
% 7.33/1.51  qbf_prep_cycles:                        0
% 7.33/1.51  
% 7.33/1.51  ------ BMC1
% 7.33/1.51  
% 7.33/1.51  bmc1_current_bound:                     -1
% 7.33/1.51  bmc1_last_solved_bound:                 -1
% 7.33/1.51  bmc1_unsat_core_size:                   -1
% 7.33/1.51  bmc1_unsat_core_parents_size:           -1
% 7.33/1.51  bmc1_merge_next_fun:                    0
% 7.33/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.33/1.51  
% 7.33/1.51  ------ Instantiation
% 7.33/1.51  
% 7.33/1.51  inst_num_of_clauses:                    2750
% 7.33/1.51  inst_num_in_passive:                    769
% 7.33/1.51  inst_num_in_active:                     853
% 7.33/1.51  inst_num_in_unprocessed:                1129
% 7.33/1.51  inst_num_of_loops:                      990
% 7.33/1.51  inst_num_of_learning_restarts:          0
% 7.33/1.51  inst_num_moves_active_passive:          133
% 7.33/1.51  inst_lit_activity:                      0
% 7.33/1.51  inst_lit_activity_moves:                0
% 7.33/1.51  inst_num_tautologies:                   0
% 7.33/1.51  inst_num_prop_implied:                  0
% 7.33/1.51  inst_num_existing_simplified:           0
% 7.33/1.51  inst_num_eq_res_simplified:             0
% 7.33/1.51  inst_num_child_elim:                    0
% 7.33/1.51  inst_num_of_dismatching_blockings:      2165
% 7.33/1.51  inst_num_of_non_proper_insts:           2975
% 7.33/1.51  inst_num_of_duplicates:                 0
% 7.33/1.51  inst_inst_num_from_inst_to_res:         0
% 7.33/1.51  inst_dismatching_checking_time:         0.
% 7.33/1.51  
% 7.33/1.51  ------ Resolution
% 7.33/1.51  
% 7.33/1.51  res_num_of_clauses:                     0
% 7.33/1.51  res_num_in_passive:                     0
% 7.33/1.51  res_num_in_active:                      0
% 7.33/1.51  res_num_of_loops:                       78
% 7.33/1.51  res_forward_subset_subsumed:            268
% 7.33/1.51  res_backward_subset_subsumed:           6
% 7.33/1.51  res_forward_subsumed:                   0
% 7.33/1.51  res_backward_subsumed:                  0
% 7.33/1.51  res_forward_subsumption_resolution:     0
% 7.33/1.51  res_backward_subsumption_resolution:    0
% 7.33/1.51  res_clause_to_clause_subsumption:       5473
% 7.33/1.51  res_orphan_elimination:                 0
% 7.33/1.51  res_tautology_del:                      385
% 7.33/1.51  res_num_eq_res_simplified:              0
% 7.33/1.51  res_num_sel_changes:                    0
% 7.33/1.51  res_moves_from_active_to_pass:          0
% 7.33/1.51  
% 7.33/1.51  ------ Superposition
% 7.33/1.51  
% 7.33/1.51  sup_time_total:                         0.
% 7.33/1.51  sup_time_generating:                    0.
% 7.33/1.51  sup_time_sim_full:                      0.
% 7.33/1.51  sup_time_sim_immed:                     0.
% 7.33/1.51  
% 7.33/1.51  sup_num_of_clauses:                     528
% 7.33/1.51  sup_num_in_active:                      131
% 7.33/1.51  sup_num_in_passive:                     397
% 7.33/1.51  sup_num_of_loops:                       197
% 7.33/1.51  sup_fw_superposition:                   923
% 7.33/1.51  sup_bw_superposition:                   828
% 7.33/1.51  sup_immediate_simplified:               1199
% 7.33/1.51  sup_given_eliminated:                   4
% 7.33/1.51  comparisons_done:                       0
% 7.33/1.51  comparisons_avoided:                    0
% 7.33/1.51  
% 7.33/1.51  ------ Simplifications
% 7.33/1.51  
% 7.33/1.51  
% 7.33/1.51  sim_fw_subset_subsumed:                 195
% 7.33/1.51  sim_bw_subset_subsumed:                 62
% 7.33/1.51  sim_fw_subsumed:                        379
% 7.33/1.51  sim_bw_subsumed:                        33
% 7.33/1.51  sim_fw_subsumption_res:                 15
% 7.33/1.51  sim_bw_subsumption_res:                 0
% 7.33/1.51  sim_tautology_del:                      31
% 7.33/1.51  sim_eq_tautology_del:                   47
% 7.33/1.51  sim_eq_res_simp:                        14
% 7.33/1.51  sim_fw_demodulated:                     300
% 7.33/1.51  sim_bw_demodulated:                     67
% 7.33/1.51  sim_light_normalised:                   445
% 7.33/1.51  sim_joinable_taut:                      0
% 7.33/1.51  sim_joinable_simp:                      0
% 7.33/1.51  sim_ac_normalised:                      0
% 7.33/1.51  sim_smt_subsumption:                    0
% 7.33/1.51  
%------------------------------------------------------------------------------
