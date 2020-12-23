%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:23 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 630 expanded)
%              Number of clauses        :   65 ( 212 expanded)
%              Number of leaves         :   15 ( 151 expanded)
%              Depth                    :   18
%              Number of atoms          :  308 (1468 expanded)
%              Number of equality atoms :  130 ( 593 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f31])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f35,f31,f31])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f38,f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f31])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f23,plain,
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

fof(f24,plain,
    ( k1_xboole_0 != sK2
    & r1_tarski(sK2,k3_subset_1(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f23])).

fof(f42,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_434,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_428,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_430,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_911,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_428,c_430])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_427,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1027,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_911,c_427])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1130,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1027,c_0])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_432,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3226,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_432])).

cnf(c_4948,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_3226])).

cnf(c_1148,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1130,c_1027])).

cnf(c_4951,plain,
    ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4948,c_1148])).

cnf(c_4952,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4951,c_1130])).

cnf(c_11676,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_434,c_4952])).

cnf(c_11684,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11676,c_1130,c_1148])).

cnf(c_12948,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11684,c_432])).

cnf(c_12987,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12948])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_431,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12947,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11684,c_431])).

cnf(c_12984,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12947])).

cnf(c_146,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_586,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_4065,plain,
    ( sK2 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_4066,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_4065])).

cnf(c_2484,plain,
    ( ~ r1_xboole_0(X0,sK3)
    | k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2486,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2484])).

cnf(c_1543,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | r1_xboole_0(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1545,plain,
    ( ~ r1_tarski(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_1495,plain,
    ( X0 != X1
    | X0 = k5_xboole_0(X2,k3_xboole_0(X2,sK3))
    | k5_xboole_0(X2,k3_xboole_0(X2,sK3)) != X1 ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_1496,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != sK2
    | sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_151,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_595,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
    | X1 != k3_subset_1(sK1,sK3)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_666,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
    | X0 != sK2
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k3_subset_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_1299,plain,
    ( r1_tarski(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
    | X0 != sK2
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) != k3_subset_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_1301,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
    | r1_tarski(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) != k3_subset_1(sK1,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_665,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_799,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_1066,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_1070,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1066])).

cnf(c_145,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_955,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_146,c_145])).

cnf(c_1035,plain,
    ( ~ r1_xboole_0(X0,X1)
    | X0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_955,c_10])).

cnf(c_1037,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_664,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_150,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_658,plain,
    ( r1_xboole_0(sK2,X0)
    | ~ r1_xboole_0(sK2,k5_xboole_0(X1,k3_xboole_0(X1,sK3)))
    | X0 != k5_xboole_0(X1,k3_xboole_0(X1,sK3)) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_660,plain,
    ( ~ r1_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)))
    | r1_xboole_0(sK2,sK2)
    | sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_587,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_581,plain,
    ( ~ r1_tarski(sK2,sK3)
    | r1_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_583,plain,
    ( ~ r1_tarski(sK2,sK3)
    | r1_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_581])).

cnf(c_164,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12987,c_12984,c_4066,c_2486,c_1545,c_1496,c_1301,c_1070,c_1037,c_664,c_660,c_587,c_583,c_164,c_13,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:22:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.65/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.99  
% 3.65/0.99  ------  iProver source info
% 3.65/0.99  
% 3.65/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.99  git: non_committed_changes: false
% 3.65/0.99  git: last_make_outside_of_git: false
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  ------ Parsing...
% 3.65/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.99  ------ Proving...
% 3.65/0.99  ------ Problem Properties 
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  clauses                                 17
% 3.65/0.99  conjectures                             4
% 3.65/0.99  EPR                                     3
% 3.65/0.99  Horn                                    13
% 3.65/0.99  unary                                   6
% 3.65/0.99  binary                                  7
% 3.65/0.99  lits                                    33
% 3.65/0.99  lits eq                                 7
% 3.65/0.99  fd_pure                                 0
% 3.65/0.99  fd_pseudo                               0
% 3.65/0.99  fd_cond                                 0
% 3.65/0.99  fd_pseudo_cond                          3
% 3.65/0.99  AC symbols                              0
% 3.65/0.99  
% 3.65/0.99  ------ Input Options Time Limit: Unbounded
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  Current options:
% 3.65/0.99  ------ 
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ Proving...
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS status Theorem for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  fof(f1,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f18,plain,(
% 3.65/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.65/0.99    inference(nnf_transformation,[],[f1])).
% 3.65/0.99  
% 3.65/0.99  fof(f19,plain,(
% 3.65/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.65/0.99    inference(flattening,[],[f18])).
% 3.65/0.99  
% 3.65/0.99  fof(f20,plain,(
% 3.65/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.65/0.99    inference(rectify,[],[f19])).
% 3.65/0.99  
% 3.65/0.99  fof(f21,plain,(
% 3.65/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f22,plain,(
% 3.65/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 3.65/0.99  
% 3.65/0.99  fof(f28,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f22])).
% 3.65/0.99  
% 3.65/0.99  fof(f2,axiom,(
% 3.65/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f31,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f2])).
% 3.65/0.99  
% 3.65/0.99  fof(f46,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.65/0.99    inference(definition_unfolding,[],[f28,f31])).
% 3.65/0.99  
% 3.65/0.99  fof(f4,axiom,(
% 3.65/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f34,plain,(
% 3.65/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f4])).
% 3.65/0.99  
% 3.65/0.99  fof(f3,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f12,plain,(
% 3.65/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.65/0.99    inference(ennf_transformation,[],[f3])).
% 3.65/0.99  
% 3.65/0.99  fof(f33,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f12])).
% 3.65/0.99  
% 3.65/0.99  fof(f50,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 3.91/0.99    inference(definition_unfolding,[],[f33,f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f6,axiom,(
% 3.91/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f11,plain,(
% 3.91/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 3.91/0.99    inference(unused_predicate_definition_removal,[],[f6])).
% 3.91/0.99  
% 3.91/0.99  fof(f13,plain,(
% 3.91/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.91/0.99    inference(ennf_transformation,[],[f11])).
% 3.91/0.99  
% 3.91/0.99  fof(f36,plain,(
% 3.91/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f13])).
% 3.91/0.99  
% 3.91/0.99  fof(f52,plain,(
% 3.91/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.91/0.99    inference(definition_unfolding,[],[f36,f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f5,axiom,(
% 3.91/0.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f35,plain,(
% 3.91/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f5])).
% 3.91/0.99  
% 3.91/0.99  fof(f43,plain,(
% 3.91/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.91/0.99    inference(definition_unfolding,[],[f35,f31,f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f26,plain,(
% 3.91/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.91/0.99    inference(cnf_transformation,[],[f22])).
% 3.91/0.99  
% 3.91/0.99  fof(f48,plain,(
% 3.91/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.91/0.99    inference(definition_unfolding,[],[f26,f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f56,plain,(
% 3.91/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.91/0.99    inference(equality_resolution,[],[f48])).
% 3.91/0.99  
% 3.91/0.99  fof(f25,plain,(
% 3.91/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.91/0.99    inference(cnf_transformation,[],[f22])).
% 3.91/0.99  
% 3.91/0.99  fof(f49,plain,(
% 3.91/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.91/0.99    inference(definition_unfolding,[],[f25,f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f57,plain,(
% 3.91/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.91/0.99    inference(equality_resolution,[],[f49])).
% 3.91/0.99  
% 3.91/0.99  fof(f8,axiom,(
% 3.91/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f15,plain,(
% 3.91/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.91/0.99    inference(ennf_transformation,[],[f8])).
% 3.91/0.99  
% 3.91/0.99  fof(f38,plain,(
% 3.91/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/0.99    inference(cnf_transformation,[],[f15])).
% 3.91/0.99  
% 3.91/0.99  fof(f54,plain,(
% 3.91/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/0.99    inference(definition_unfolding,[],[f38,f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f7,axiom,(
% 3.91/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f14,plain,(
% 3.91/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.91/0.99    inference(ennf_transformation,[],[f7])).
% 3.91/0.99  
% 3.91/0.99  fof(f37,plain,(
% 3.91/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.91/0.99    inference(cnf_transformation,[],[f14])).
% 3.91/0.99  
% 3.91/0.99  fof(f53,plain,(
% 3.91/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.91/0.99    inference(definition_unfolding,[],[f37,f31])).
% 3.91/0.99  
% 3.91/0.99  fof(f9,conjecture,(
% 3.91/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 3.91/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.91/0.99  
% 3.91/0.99  fof(f10,negated_conjecture,(
% 3.91/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 3.91/0.99    inference(negated_conjecture,[],[f9])).
% 3.91/0.99  
% 3.91/0.99  fof(f16,plain,(
% 3.91/0.99    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.91/0.99    inference(ennf_transformation,[],[f10])).
% 3.91/0.99  
% 3.91/0.99  fof(f17,plain,(
% 3.91/0.99    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.91/0.99    inference(flattening,[],[f16])).
% 3.91/0.99  
% 3.91/0.99  fof(f23,plain,(
% 3.91/0.99    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 3.91/0.99    introduced(choice_axiom,[])).
% 3.91/0.99  
% 3.91/0.99  fof(f24,plain,(
% 3.91/0.99    k1_xboole_0 != sK2 & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.91/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f23])).
% 3.91/0.99  
% 3.91/0.99  fof(f42,plain,(
% 3.91/0.99    k1_xboole_0 != sK2),
% 3.91/0.99    inference(cnf_transformation,[],[f24])).
% 3.91/0.99  
% 3.91/0.99  fof(f41,plain,(
% 3.91/0.99    r1_tarski(sK2,k3_subset_1(sK1,sK3))),
% 3.91/0.99    inference(cnf_transformation,[],[f24])).
% 3.91/0.99  
% 3.91/0.99  fof(f40,plain,(
% 3.91/0.99    r1_tarski(sK2,sK3)),
% 3.91/0.99    inference(cnf_transformation,[],[f24])).
% 3.91/0.99  
% 3.91/0.99  fof(f39,plain,(
% 3.91/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.91/0.99    inference(cnf_transformation,[],[f24])).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3,plain,
% 3.91/0.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.91/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.91/0.99      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 3.91/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_434,plain,
% 3.91/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 3.91/0.99      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 3.91/0.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_9,plain,
% 3.91/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.91/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_428,plain,
% 3.91/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_7,plain,
% 3.91/0.99      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 3.91/0.99      | r1_xboole_0(X0,X2) ),
% 3.91/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_430,plain,
% 3.91/0.99      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 3.91/0.99      | r1_xboole_0(X0,X2) = iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_911,plain,
% 3.91/0.99      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_428,c_430]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_10,plain,
% 3.91/0.99      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 3.91/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_427,plain,
% 3.91/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 3.91/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1027,plain,
% 3.91/0.99      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_911,c_427]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_0,plain,
% 3.91/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.91/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1130,plain,
% 3.91/0.99      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_1027,c_0]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_5,plain,
% 3.91/0.99      ( ~ r2_hidden(X0,X1)
% 3.91/0.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.91/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_432,plain,
% 3.91/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.91/0.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_3226,plain,
% 3.91/0.99      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 3.91/0.99      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_0,c_432]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_4948,plain,
% 3.91/0.99      ( r2_hidden(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.91/0.99      | r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_1130,c_3226]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1148,plain,
% 3.91/0.99      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.91/0.99      inference(demodulation,[status(thm)],[c_1130,c_1027]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_4951,plain,
% 3.91/0.99      ( r2_hidden(X0,k3_xboole_0(k1_xboole_0,X1)) != iProver_top
% 3.91/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.91/0.99      inference(light_normalisation,[status(thm)],[c_4948,c_1148]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_4952,plain,
% 3.91/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.91/0.99      inference(demodulation,[status(thm)],[c_4951,c_1130]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_11676,plain,
% 3.91/0.99      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = X1
% 3.91/0.99      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_434,c_4952]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_11684,plain,
% 3.91/0.99      ( k1_xboole_0 = X0
% 3.91/0.99      | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 3.91/0.99      inference(light_normalisation,
% 3.91/0.99                [status(thm)],
% 3.91/0.99                [c_11676,c_1130,c_1148]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_12948,plain,
% 3.91/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.91/0.99      | r2_hidden(sK0(k1_xboole_0,X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X1) != iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_11684,c_432]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_12987,plain,
% 3.91/0.99      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k1_xboole_0
% 3.91/0.99      | r2_hidden(sK0(k1_xboole_0,sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))),sK2) != iProver_top ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_12948]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_6,plain,
% 3.91/0.99      ( r2_hidden(X0,X1)
% 3.91/0.99      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.91/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_431,plain,
% 3.91/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.91/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top ),
% 3.91/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_12947,plain,
% 3.91/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.91/0.99      | r2_hidden(sK0(k1_xboole_0,X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0) = iProver_top ),
% 3.91/0.99      inference(superposition,[status(thm)],[c_11684,c_431]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_12984,plain,
% 3.91/0.99      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k1_xboole_0
% 3.91/0.99      | r2_hidden(sK0(k1_xboole_0,sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))),sK2) = iProver_top ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_12947]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_146,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_586,plain,
% 3.91/0.99      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_146]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_4065,plain,
% 3.91/0.99      ( sK2 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 3.91/0.99      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 3.91/0.99      | k1_xboole_0 = sK2 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_586]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_4066,plain,
% 3.91/0.99      ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
% 3.91/0.99      | k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
% 3.91/0.99      | k1_xboole_0 = sK2 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_4065]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_2484,plain,
% 3.91/0.99      ( ~ r1_xboole_0(X0,sK3)
% 3.91/0.99      | k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = X0 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_2486,plain,
% 3.91/0.99      ( ~ r1_xboole_0(sK2,sK3)
% 3.91/0.99      | k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK2 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_2484]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1543,plain,
% 3.91/0.99      ( ~ r1_tarski(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
% 3.91/0.99      | r1_xboole_0(X0,sK3) ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1545,plain,
% 3.91/0.99      ( ~ r1_tarski(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
% 3.91/0.99      | r1_xboole_0(sK2,sK3) ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_1543]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1495,plain,
% 3.91/0.99      ( X0 != X1
% 3.91/0.99      | X0 = k5_xboole_0(X2,k3_xboole_0(X2,sK3))
% 3.91/0.99      | k5_xboole_0(X2,k3_xboole_0(X2,sK3)) != X1 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_146]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1496,plain,
% 3.91/0.99      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) != sK2
% 3.91/0.99      | sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))
% 3.91/0.99      | sK2 != sK2 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_1495]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_151,plain,
% 3.91/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.91/0.99      theory(equality) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_595,plain,
% 3.91/0.99      ( r1_tarski(X0,X1)
% 3.91/0.99      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
% 3.91/0.99      | X1 != k3_subset_1(sK1,sK3)
% 3.91/0.99      | X0 != sK2 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_151]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_666,plain,
% 3.91/0.99      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 3.91/0.99      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
% 3.91/0.99      | X0 != sK2
% 3.91/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k3_subset_1(sK1,sK3) ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_595]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1299,plain,
% 3.91/0.99      ( r1_tarski(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
% 3.91/0.99      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
% 3.91/0.99      | X0 != sK2
% 3.91/0.99      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) != k3_subset_1(sK1,sK3) ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_666]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1301,plain,
% 3.91/0.99      ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK3))
% 3.91/0.99      | r1_tarski(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
% 3.91/0.99      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) != k3_subset_1(sK1,sK3)
% 3.91/0.99      | sK2 != sK2 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_1299]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_665,plain,
% 3.91/0.99      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_146]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_799,plain,
% 3.91/0.99      ( X0 != k1_xboole_0
% 3.91/0.99      | k1_xboole_0 = X0
% 3.91/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_665]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1066,plain,
% 3.91/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 3.91/0.99      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 3.91/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_799]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1070,plain,
% 3.91/0.99      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) != k1_xboole_0
% 3.91/0.99      | k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2))
% 3.91/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_1066]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_145,plain,( X0 = X0 ),theory(equality) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_955,plain,
% 3.91/0.99      ( X0 != X1 | X1 = X0 ),
% 3.91/0.99      inference(resolution,[status(thm)],[c_146,c_145]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1035,plain,
% 3.91/0.99      ( ~ r1_xboole_0(X0,X1) | X0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 3.91/0.99      inference(resolution,[status(thm)],[c_955,c_10]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_1037,plain,
% 3.91/0.99      ( ~ r1_xboole_0(sK2,sK2)
% 3.91/0.99      | sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_1035]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_664,plain,
% 3.91/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_145]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_150,plain,
% 3.91/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,X2) | X2 != X1 ),
% 3.91/0.99      theory(equality) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_658,plain,
% 3.91/0.99      ( r1_xboole_0(sK2,X0)
% 3.91/0.99      | ~ r1_xboole_0(sK2,k5_xboole_0(X1,k3_xboole_0(X1,sK3)))
% 3.91/0.99      | X0 != k5_xboole_0(X1,k3_xboole_0(X1,sK3)) ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_150]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_660,plain,
% 3.91/0.99      ( ~ r1_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)))
% 3.91/0.99      | r1_xboole_0(sK2,sK2)
% 3.91/0.99      | sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_658]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_12,plain,
% 3.91/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.91/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.91/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_587,plain,
% 3.91/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 3.91/0.99      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_11,plain,
% 3.91/0.99      ( ~ r1_tarski(X0,X1)
% 3.91/0.99      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.91/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_581,plain,
% 3.91/0.99      ( ~ r1_tarski(sK2,sK3)
% 3.91/0.99      | r1_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK3))) ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_583,plain,
% 3.91/0.99      ( ~ r1_tarski(sK2,sK3)
% 3.91/0.99      | r1_xboole_0(sK2,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_581]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_164,plain,
% 3.91/0.99      ( sK2 = sK2 ),
% 3.91/0.99      inference(instantiation,[status(thm)],[c_145]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_13,negated_conjecture,
% 3.91/0.99      ( k1_xboole_0 != sK2 ),
% 3.91/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_14,negated_conjecture,
% 3.91/0.99      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
% 3.91/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_15,negated_conjecture,
% 3.91/0.99      ( r1_tarski(sK2,sK3) ),
% 3.91/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(c_16,negated_conjecture,
% 3.91/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.91/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.91/0.99  
% 3.91/0.99  cnf(contradiction,plain,
% 3.91/0.99      ( $false ),
% 3.91/0.99      inference(minisat,
% 3.91/0.99                [status(thm)],
% 3.91/0.99                [c_12987,c_12984,c_4066,c_2486,c_1545,c_1496,c_1301,
% 3.91/0.99                 c_1070,c_1037,c_664,c_660,c_587,c_583,c_164,c_13,c_14,
% 3.91/0.99                 c_15,c_16]) ).
% 3.91/0.99  
% 3.91/0.99  
% 3.91/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.91/0.99  
% 3.91/0.99  ------                               Statistics
% 3.91/0.99  
% 3.91/0.99  ------ Selected
% 3.91/0.99  
% 3.91/0.99  total_time:                             0.407
% 3.91/0.99  
%------------------------------------------------------------------------------
