%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:43 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 181 expanded)
%              Number of clauses        :   56 (  62 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  283 ( 534 expanded)
%              Number of equality atoms :   86 ( 129 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(sK3,k3_subset_1(X0,X1))
        & r1_tarski(X1,k3_subset_1(X0,sK3))
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK1,sK2))
          & r1_tarski(sK2,k3_subset_1(sK1,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(sK3,k3_subset_1(sK1,sK2))
    & r1_tarski(sK2,k3_subset_1(sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f29,f28])).

fof(f52,plain,(
    r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f34])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f34])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ~ r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1311,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1300,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_495,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_496,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_1475,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_496])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1310,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2788,plain,
    ( r1_xboole_0(X0,sK3) = iProver_top
    | r1_tarski(X0,k3_subset_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_1310])).

cnf(c_3320,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_2788])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1306,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1308,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1312,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2819,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1312])).

cnf(c_10233,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1306,c_2819])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12493,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10233,c_69])).

cnf(c_12494,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12493])).

cnf(c_12510,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_3320,c_12494])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1307,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13205,plain,
    ( r1_xboole_0(X0,sK2) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12510,c_1307])).

cnf(c_13839,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1311,c_13205])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_504,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_505,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_1476,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_505])).

cnf(c_3616,plain,
    ( r1_xboole_0(X0,sK2) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1306])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1301,plain,
    ( r1_tarski(sK3,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4257,plain,
    ( r1_xboole_0(sK3,sK2) != iProver_top
    | r1_tarski(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3616,c_1301])).

cnf(c_926,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_933,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_926])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_169,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_170,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_169])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_459,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_460,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_462,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_27])).

cnf(c_604,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_170,c_462])).

cnf(c_605,plain,
    ( r1_tarski(sK3,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_606,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_608,plain,
    ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
    | r1_tarski(sK3,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_74,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_70,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13839,c_4257,c_933,c_608,c_74,c_70])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.89/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/1.06  
% 3.89/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/1.06  
% 3.89/1.06  ------  iProver source info
% 3.89/1.06  
% 3.89/1.06  git: date: 2020-06-30 10:37:57 +0100
% 3.89/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/1.06  git: non_committed_changes: false
% 3.89/1.06  git: last_make_outside_of_git: false
% 3.89/1.06  
% 3.89/1.06  ------ 
% 3.89/1.06  
% 3.89/1.06  ------ Input Options
% 3.89/1.06  
% 3.89/1.06  --out_options                           all
% 3.89/1.06  --tptp_safe_out                         true
% 3.89/1.06  --problem_path                          ""
% 3.89/1.06  --include_path                          ""
% 3.89/1.06  --clausifier                            res/vclausify_rel
% 3.89/1.06  --clausifier_options                    ""
% 3.89/1.06  --stdin                                 false
% 3.89/1.06  --stats_out                             all
% 3.89/1.06  
% 3.89/1.06  ------ General Options
% 3.89/1.06  
% 3.89/1.06  --fof                                   false
% 3.89/1.06  --time_out_real                         305.
% 3.89/1.06  --time_out_virtual                      -1.
% 3.89/1.06  --symbol_type_check                     false
% 3.89/1.06  --clausify_out                          false
% 3.89/1.06  --sig_cnt_out                           false
% 3.89/1.06  --trig_cnt_out                          false
% 3.89/1.06  --trig_cnt_out_tolerance                1.
% 3.89/1.06  --trig_cnt_out_sk_spl                   false
% 3.89/1.06  --abstr_cl_out                          false
% 3.89/1.06  
% 3.89/1.06  ------ Global Options
% 3.89/1.06  
% 3.89/1.06  --schedule                              default
% 3.89/1.06  --add_important_lit                     false
% 3.89/1.06  --prop_solver_per_cl                    1000
% 3.89/1.06  --min_unsat_core                        false
% 3.89/1.06  --soft_assumptions                      false
% 3.89/1.06  --soft_lemma_size                       3
% 3.89/1.06  --prop_impl_unit_size                   0
% 3.89/1.06  --prop_impl_unit                        []
% 3.89/1.06  --share_sel_clauses                     true
% 3.89/1.06  --reset_solvers                         false
% 3.89/1.06  --bc_imp_inh                            [conj_cone]
% 3.89/1.06  --conj_cone_tolerance                   3.
% 3.89/1.06  --extra_neg_conj                        none
% 3.89/1.06  --large_theory_mode                     true
% 3.89/1.06  --prolific_symb_bound                   200
% 3.89/1.06  --lt_threshold                          2000
% 3.89/1.06  --clause_weak_htbl                      true
% 3.89/1.06  --gc_record_bc_elim                     false
% 3.89/1.06  
% 3.89/1.06  ------ Preprocessing Options
% 3.89/1.06  
% 3.89/1.06  --preprocessing_flag                    true
% 3.89/1.06  --time_out_prep_mult                    0.1
% 3.89/1.06  --splitting_mode                        input
% 3.89/1.06  --splitting_grd                         true
% 3.89/1.06  --splitting_cvd                         false
% 3.89/1.06  --splitting_cvd_svl                     false
% 3.89/1.06  --splitting_nvd                         32
% 3.89/1.06  --sub_typing                            true
% 3.89/1.06  --prep_gs_sim                           true
% 3.89/1.06  --prep_unflatten                        true
% 3.89/1.06  --prep_res_sim                          true
% 3.89/1.06  --prep_upred                            true
% 3.89/1.06  --prep_sem_filter                       exhaustive
% 3.89/1.06  --prep_sem_filter_out                   false
% 3.89/1.06  --pred_elim                             true
% 3.89/1.06  --res_sim_input                         true
% 3.89/1.06  --eq_ax_congr_red                       true
% 3.89/1.06  --pure_diseq_elim                       true
% 3.89/1.06  --brand_transform                       false
% 3.89/1.06  --non_eq_to_eq                          false
% 3.89/1.06  --prep_def_merge                        true
% 3.89/1.06  --prep_def_merge_prop_impl              false
% 3.89/1.06  --prep_def_merge_mbd                    true
% 3.89/1.06  --prep_def_merge_tr_red                 false
% 3.89/1.06  --prep_def_merge_tr_cl                  false
% 3.89/1.06  --smt_preprocessing                     true
% 3.89/1.06  --smt_ac_axioms                         fast
% 3.89/1.06  --preprocessed_out                      false
% 3.89/1.06  --preprocessed_stats                    false
% 3.89/1.06  
% 3.89/1.06  ------ Abstraction refinement Options
% 3.89/1.06  
% 3.89/1.06  --abstr_ref                             []
% 3.89/1.06  --abstr_ref_prep                        false
% 3.89/1.06  --abstr_ref_until_sat                   false
% 3.89/1.06  --abstr_ref_sig_restrict                funpre
% 3.89/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/1.06  --abstr_ref_under                       []
% 3.89/1.06  
% 3.89/1.06  ------ SAT Options
% 3.89/1.06  
% 3.89/1.06  --sat_mode                              false
% 3.89/1.06  --sat_fm_restart_options                ""
% 3.89/1.06  --sat_gr_def                            false
% 3.89/1.06  --sat_epr_types                         true
% 3.89/1.06  --sat_non_cyclic_types                  false
% 3.89/1.06  --sat_finite_models                     false
% 3.89/1.06  --sat_fm_lemmas                         false
% 3.89/1.06  --sat_fm_prep                           false
% 3.89/1.06  --sat_fm_uc_incr                        true
% 3.89/1.06  --sat_out_model                         small
% 3.89/1.06  --sat_out_clauses                       false
% 3.89/1.06  
% 3.89/1.06  ------ QBF Options
% 3.89/1.06  
% 3.89/1.06  --qbf_mode                              false
% 3.89/1.06  --qbf_elim_univ                         false
% 3.89/1.06  --qbf_dom_inst                          none
% 3.89/1.06  --qbf_dom_pre_inst                      false
% 3.89/1.06  --qbf_sk_in                             false
% 3.89/1.06  --qbf_pred_elim                         true
% 3.89/1.06  --qbf_split                             512
% 3.89/1.06  
% 3.89/1.06  ------ BMC1 Options
% 3.89/1.06  
% 3.89/1.06  --bmc1_incremental                      false
% 3.89/1.06  --bmc1_axioms                           reachable_all
% 3.89/1.06  --bmc1_min_bound                        0
% 3.89/1.06  --bmc1_max_bound                        -1
% 3.89/1.06  --bmc1_max_bound_default                -1
% 3.89/1.06  --bmc1_symbol_reachability              true
% 3.89/1.06  --bmc1_property_lemmas                  false
% 3.89/1.06  --bmc1_k_induction                      false
% 3.89/1.06  --bmc1_non_equiv_states                 false
% 3.89/1.06  --bmc1_deadlock                         false
% 3.89/1.06  --bmc1_ucm                              false
% 3.89/1.06  --bmc1_add_unsat_core                   none
% 3.89/1.06  --bmc1_unsat_core_children              false
% 3.89/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/1.06  --bmc1_out_stat                         full
% 3.89/1.06  --bmc1_ground_init                      false
% 3.89/1.06  --bmc1_pre_inst_next_state              false
% 3.89/1.06  --bmc1_pre_inst_state                   false
% 3.89/1.06  --bmc1_pre_inst_reach_state             false
% 3.89/1.06  --bmc1_out_unsat_core                   false
% 3.89/1.06  --bmc1_aig_witness_out                  false
% 3.89/1.06  --bmc1_verbose                          false
% 3.89/1.06  --bmc1_dump_clauses_tptp                false
% 3.89/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.89/1.06  --bmc1_dump_file                        -
% 3.89/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.89/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.89/1.06  --bmc1_ucm_extend_mode                  1
% 3.89/1.06  --bmc1_ucm_init_mode                    2
% 3.89/1.06  --bmc1_ucm_cone_mode                    none
% 3.89/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.89/1.06  --bmc1_ucm_relax_model                  4
% 3.89/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.89/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/1.06  --bmc1_ucm_layered_model                none
% 3.89/1.06  --bmc1_ucm_max_lemma_size               10
% 3.89/1.06  
% 3.89/1.06  ------ AIG Options
% 3.89/1.06  
% 3.89/1.06  --aig_mode                              false
% 3.89/1.06  
% 3.89/1.06  ------ Instantiation Options
% 3.89/1.06  
% 3.89/1.06  --instantiation_flag                    true
% 3.89/1.06  --inst_sos_flag                         true
% 3.89/1.06  --inst_sos_phase                        true
% 3.89/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/1.06  --inst_lit_sel_side                     num_symb
% 3.89/1.06  --inst_solver_per_active                1400
% 3.89/1.06  --inst_solver_calls_frac                1.
% 3.89/1.06  --inst_passive_queue_type               priority_queues
% 3.89/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/1.06  --inst_passive_queues_freq              [25;2]
% 3.89/1.06  --inst_dismatching                      true
% 3.89/1.06  --inst_eager_unprocessed_to_passive     true
% 3.89/1.06  --inst_prop_sim_given                   true
% 3.89/1.06  --inst_prop_sim_new                     false
% 3.89/1.06  --inst_subs_new                         false
% 3.89/1.06  --inst_eq_res_simp                      false
% 3.89/1.06  --inst_subs_given                       false
% 3.89/1.06  --inst_orphan_elimination               true
% 3.89/1.06  --inst_learning_loop_flag               true
% 3.89/1.06  --inst_learning_start                   3000
% 3.89/1.06  --inst_learning_factor                  2
% 3.89/1.06  --inst_start_prop_sim_after_learn       3
% 3.89/1.06  --inst_sel_renew                        solver
% 3.89/1.06  --inst_lit_activity_flag                true
% 3.89/1.06  --inst_restr_to_given                   false
% 3.89/1.06  --inst_activity_threshold               500
% 3.89/1.06  --inst_out_proof                        true
% 3.89/1.06  
% 3.89/1.06  ------ Resolution Options
% 3.89/1.06  
% 3.89/1.06  --resolution_flag                       true
% 3.89/1.06  --res_lit_sel                           adaptive
% 3.89/1.06  --res_lit_sel_side                      none
% 3.89/1.06  --res_ordering                          kbo
% 3.89/1.06  --res_to_prop_solver                    active
% 3.89/1.06  --res_prop_simpl_new                    false
% 3.89/1.06  --res_prop_simpl_given                  true
% 3.89/1.06  --res_passive_queue_type                priority_queues
% 3.89/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/1.06  --res_passive_queues_freq               [15;5]
% 3.89/1.06  --res_forward_subs                      full
% 3.89/1.06  --res_backward_subs                     full
% 3.89/1.06  --res_forward_subs_resolution           true
% 3.89/1.06  --res_backward_subs_resolution          true
% 3.89/1.06  --res_orphan_elimination                true
% 3.89/1.06  --res_time_limit                        2.
% 3.89/1.06  --res_out_proof                         true
% 3.89/1.06  
% 3.89/1.06  ------ Superposition Options
% 3.89/1.06  
% 3.89/1.06  --superposition_flag                    true
% 3.89/1.06  --sup_passive_queue_type                priority_queues
% 3.89/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.89/1.06  --demod_completeness_check              fast
% 3.89/1.06  --demod_use_ground                      true
% 3.89/1.06  --sup_to_prop_solver                    passive
% 3.89/1.06  --sup_prop_simpl_new                    true
% 3.89/1.06  --sup_prop_simpl_given                  true
% 3.89/1.06  --sup_fun_splitting                     true
% 3.89/1.06  --sup_smt_interval                      50000
% 3.89/1.06  
% 3.89/1.06  ------ Superposition Simplification Setup
% 3.89/1.06  
% 3.89/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.89/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.89/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.89/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.89/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.89/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.89/1.06  --sup_immed_triv                        [TrivRules]
% 3.89/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/1.06  --sup_immed_bw_main                     []
% 3.89/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.89/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/1.06  --sup_input_bw                          []
% 3.89/1.06  
% 3.89/1.06  ------ Combination Options
% 3.89/1.06  
% 3.89/1.06  --comb_res_mult                         3
% 3.89/1.06  --comb_sup_mult                         2
% 3.89/1.06  --comb_inst_mult                        10
% 3.89/1.06  
% 3.89/1.06  ------ Debug Options
% 3.89/1.06  
% 3.89/1.06  --dbg_backtrace                         false
% 3.89/1.06  --dbg_dump_prop_clauses                 false
% 3.89/1.06  --dbg_dump_prop_clauses_file            -
% 3.89/1.06  --dbg_out_stat                          false
% 3.89/1.06  ------ Parsing...
% 3.89/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/1.06  
% 3.89/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.89/1.06  
% 3.89/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/1.06  
% 3.89/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.06  ------ Proving...
% 3.89/1.06  ------ Problem Properties 
% 3.89/1.06  
% 3.89/1.06  
% 3.89/1.06  clauses                                 18
% 3.89/1.06  conjectures                             2
% 3.89/1.06  EPR                                     2
% 3.89/1.06  Horn                                    17
% 3.89/1.06  unary                                   6
% 3.89/1.06  binary                                  8
% 3.89/1.06  lits                                    34
% 3.89/1.06  lits eq                                 8
% 3.89/1.06  fd_pure                                 0
% 3.89/1.06  fd_pseudo                               0
% 3.89/1.06  fd_cond                                 0
% 3.89/1.06  fd_pseudo_cond                          3
% 3.89/1.06  AC symbols                              0
% 3.89/1.06  
% 3.89/1.06  ------ Schedule dynamic 5 is on 
% 3.89/1.06  
% 3.89/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.89/1.06  
% 3.89/1.06  
% 3.89/1.06  ------ 
% 3.89/1.06  Current options:
% 3.89/1.06  ------ 
% 3.89/1.06  
% 3.89/1.06  ------ Input Options
% 3.89/1.06  
% 3.89/1.06  --out_options                           all
% 3.89/1.06  --tptp_safe_out                         true
% 3.89/1.06  --problem_path                          ""
% 3.89/1.06  --include_path                          ""
% 3.89/1.06  --clausifier                            res/vclausify_rel
% 3.89/1.06  --clausifier_options                    ""
% 3.89/1.06  --stdin                                 false
% 3.89/1.06  --stats_out                             all
% 3.89/1.06  
% 3.89/1.06  ------ General Options
% 3.89/1.06  
% 3.89/1.06  --fof                                   false
% 3.89/1.06  --time_out_real                         305.
% 3.89/1.06  --time_out_virtual                      -1.
% 3.89/1.06  --symbol_type_check                     false
% 3.89/1.06  --clausify_out                          false
% 3.89/1.06  --sig_cnt_out                           false
% 3.89/1.06  --trig_cnt_out                          false
% 3.89/1.06  --trig_cnt_out_tolerance                1.
% 3.89/1.06  --trig_cnt_out_sk_spl                   false
% 3.89/1.06  --abstr_cl_out                          false
% 3.89/1.06  
% 3.89/1.06  ------ Global Options
% 3.89/1.06  
% 3.89/1.06  --schedule                              default
% 3.89/1.06  --add_important_lit                     false
% 3.89/1.06  --prop_solver_per_cl                    1000
% 3.89/1.06  --min_unsat_core                        false
% 3.89/1.06  --soft_assumptions                      false
% 3.89/1.06  --soft_lemma_size                       3
% 3.89/1.06  --prop_impl_unit_size                   0
% 3.89/1.06  --prop_impl_unit                        []
% 3.89/1.06  --share_sel_clauses                     true
% 3.89/1.06  --reset_solvers                         false
% 3.89/1.06  --bc_imp_inh                            [conj_cone]
% 3.89/1.06  --conj_cone_tolerance                   3.
% 3.89/1.06  --extra_neg_conj                        none
% 3.89/1.06  --large_theory_mode                     true
% 3.89/1.06  --prolific_symb_bound                   200
% 3.89/1.06  --lt_threshold                          2000
% 3.89/1.06  --clause_weak_htbl                      true
% 3.89/1.06  --gc_record_bc_elim                     false
% 3.89/1.06  
% 3.89/1.06  ------ Preprocessing Options
% 3.89/1.06  
% 3.89/1.06  --preprocessing_flag                    true
% 3.89/1.06  --time_out_prep_mult                    0.1
% 3.89/1.06  --splitting_mode                        input
% 3.89/1.06  --splitting_grd                         true
% 3.89/1.06  --splitting_cvd                         false
% 3.89/1.06  --splitting_cvd_svl                     false
% 3.89/1.06  --splitting_nvd                         32
% 3.89/1.06  --sub_typing                            true
% 3.89/1.06  --prep_gs_sim                           true
% 3.89/1.06  --prep_unflatten                        true
% 3.89/1.06  --prep_res_sim                          true
% 3.89/1.06  --prep_upred                            true
% 3.89/1.06  --prep_sem_filter                       exhaustive
% 3.89/1.06  --prep_sem_filter_out                   false
% 3.89/1.06  --pred_elim                             true
% 3.89/1.06  --res_sim_input                         true
% 3.89/1.06  --eq_ax_congr_red                       true
% 3.89/1.06  --pure_diseq_elim                       true
% 3.89/1.06  --brand_transform                       false
% 3.89/1.06  --non_eq_to_eq                          false
% 3.89/1.06  --prep_def_merge                        true
% 3.89/1.06  --prep_def_merge_prop_impl              false
% 3.89/1.06  --prep_def_merge_mbd                    true
% 3.89/1.06  --prep_def_merge_tr_red                 false
% 3.89/1.06  --prep_def_merge_tr_cl                  false
% 3.89/1.06  --smt_preprocessing                     true
% 3.89/1.06  --smt_ac_axioms                         fast
% 3.89/1.06  --preprocessed_out                      false
% 3.89/1.06  --preprocessed_stats                    false
% 3.89/1.06  
% 3.89/1.06  ------ Abstraction refinement Options
% 3.89/1.06  
% 3.89/1.06  --abstr_ref                             []
% 3.89/1.06  --abstr_ref_prep                        false
% 3.89/1.06  --abstr_ref_until_sat                   false
% 3.89/1.06  --abstr_ref_sig_restrict                funpre
% 3.89/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/1.06  --abstr_ref_under                       []
% 3.89/1.06  
% 3.89/1.06  ------ SAT Options
% 3.89/1.06  
% 3.89/1.06  --sat_mode                              false
% 3.89/1.06  --sat_fm_restart_options                ""
% 3.89/1.06  --sat_gr_def                            false
% 3.89/1.06  --sat_epr_types                         true
% 3.89/1.06  --sat_non_cyclic_types                  false
% 3.89/1.06  --sat_finite_models                     false
% 3.89/1.06  --sat_fm_lemmas                         false
% 3.89/1.06  --sat_fm_prep                           false
% 3.89/1.06  --sat_fm_uc_incr                        true
% 3.89/1.06  --sat_out_model                         small
% 3.89/1.06  --sat_out_clauses                       false
% 3.89/1.06  
% 3.89/1.06  ------ QBF Options
% 3.89/1.06  
% 3.89/1.06  --qbf_mode                              false
% 3.89/1.06  --qbf_elim_univ                         false
% 3.89/1.06  --qbf_dom_inst                          none
% 3.89/1.06  --qbf_dom_pre_inst                      false
% 3.89/1.06  --qbf_sk_in                             false
% 3.89/1.06  --qbf_pred_elim                         true
% 3.89/1.06  --qbf_split                             512
% 3.89/1.06  
% 3.89/1.06  ------ BMC1 Options
% 3.89/1.06  
% 3.89/1.06  --bmc1_incremental                      false
% 3.89/1.06  --bmc1_axioms                           reachable_all
% 3.89/1.06  --bmc1_min_bound                        0
% 3.89/1.06  --bmc1_max_bound                        -1
% 3.89/1.06  --bmc1_max_bound_default                -1
% 3.89/1.06  --bmc1_symbol_reachability              true
% 3.89/1.06  --bmc1_property_lemmas                  false
% 3.89/1.06  --bmc1_k_induction                      false
% 3.89/1.06  --bmc1_non_equiv_states                 false
% 3.89/1.06  --bmc1_deadlock                         false
% 3.89/1.06  --bmc1_ucm                              false
% 3.89/1.06  --bmc1_add_unsat_core                   none
% 3.89/1.06  --bmc1_unsat_core_children              false
% 3.89/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/1.06  --bmc1_out_stat                         full
% 3.89/1.06  --bmc1_ground_init                      false
% 3.89/1.06  --bmc1_pre_inst_next_state              false
% 3.89/1.06  --bmc1_pre_inst_state                   false
% 3.89/1.06  --bmc1_pre_inst_reach_state             false
% 3.89/1.06  --bmc1_out_unsat_core                   false
% 3.89/1.06  --bmc1_aig_witness_out                  false
% 3.89/1.06  --bmc1_verbose                          false
% 3.89/1.06  --bmc1_dump_clauses_tptp                false
% 3.89/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.89/1.06  --bmc1_dump_file                        -
% 3.89/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.89/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.89/1.06  --bmc1_ucm_extend_mode                  1
% 3.89/1.06  --bmc1_ucm_init_mode                    2
% 3.89/1.06  --bmc1_ucm_cone_mode                    none
% 3.89/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.89/1.06  --bmc1_ucm_relax_model                  4
% 3.89/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.89/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/1.06  --bmc1_ucm_layered_model                none
% 3.89/1.06  --bmc1_ucm_max_lemma_size               10
% 3.89/1.06  
% 3.89/1.06  ------ AIG Options
% 3.89/1.06  
% 3.89/1.06  --aig_mode                              false
% 3.89/1.06  
% 3.89/1.06  ------ Instantiation Options
% 3.89/1.06  
% 3.89/1.06  --instantiation_flag                    true
% 3.89/1.06  --inst_sos_flag                         true
% 3.89/1.06  --inst_sos_phase                        true
% 3.89/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/1.06  --inst_lit_sel_side                     none
% 3.89/1.06  --inst_solver_per_active                1400
% 3.89/1.06  --inst_solver_calls_frac                1.
% 3.89/1.06  --inst_passive_queue_type               priority_queues
% 3.89/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/1.06  --inst_passive_queues_freq              [25;2]
% 3.89/1.06  --inst_dismatching                      true
% 3.89/1.06  --inst_eager_unprocessed_to_passive     true
% 3.89/1.06  --inst_prop_sim_given                   true
% 3.89/1.06  --inst_prop_sim_new                     false
% 3.89/1.06  --inst_subs_new                         false
% 3.89/1.06  --inst_eq_res_simp                      false
% 3.89/1.06  --inst_subs_given                       false
% 3.89/1.06  --inst_orphan_elimination               true
% 3.89/1.06  --inst_learning_loop_flag               true
% 3.89/1.06  --inst_learning_start                   3000
% 3.89/1.06  --inst_learning_factor                  2
% 3.89/1.06  --inst_start_prop_sim_after_learn       3
% 3.89/1.06  --inst_sel_renew                        solver
% 3.89/1.06  --inst_lit_activity_flag                true
% 3.89/1.06  --inst_restr_to_given                   false
% 3.89/1.06  --inst_activity_threshold               500
% 3.89/1.06  --inst_out_proof                        true
% 3.89/1.06  
% 3.89/1.06  ------ Resolution Options
% 3.89/1.06  
% 3.89/1.06  --resolution_flag                       false
% 3.89/1.06  --res_lit_sel                           adaptive
% 3.89/1.06  --res_lit_sel_side                      none
% 3.89/1.06  --res_ordering                          kbo
% 3.89/1.06  --res_to_prop_solver                    active
% 3.89/1.06  --res_prop_simpl_new                    false
% 3.89/1.06  --res_prop_simpl_given                  true
% 3.89/1.06  --res_passive_queue_type                priority_queues
% 3.89/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/1.06  --res_passive_queues_freq               [15;5]
% 3.89/1.06  --res_forward_subs                      full
% 3.89/1.06  --res_backward_subs                     full
% 3.89/1.06  --res_forward_subs_resolution           true
% 3.89/1.06  --res_backward_subs_resolution          true
% 3.89/1.06  --res_orphan_elimination                true
% 3.89/1.06  --res_time_limit                        2.
% 3.89/1.06  --res_out_proof                         true
% 3.89/1.06  
% 3.89/1.06  ------ Superposition Options
% 3.89/1.06  
% 3.89/1.06  --superposition_flag                    true
% 3.89/1.06  --sup_passive_queue_type                priority_queues
% 3.89/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.89/1.06  --demod_completeness_check              fast
% 3.89/1.06  --demod_use_ground                      true
% 3.89/1.06  --sup_to_prop_solver                    passive
% 3.89/1.06  --sup_prop_simpl_new                    true
% 3.89/1.06  --sup_prop_simpl_given                  true
% 3.89/1.06  --sup_fun_splitting                     true
% 3.89/1.06  --sup_smt_interval                      50000
% 3.89/1.06  
% 3.89/1.06  ------ Superposition Simplification Setup
% 3.89/1.06  
% 3.89/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.89/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.89/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.89/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.89/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.89/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.89/1.06  --sup_immed_triv                        [TrivRules]
% 3.89/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/1.06  --sup_immed_bw_main                     []
% 3.89/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.89/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/1.06  --sup_input_bw                          []
% 3.89/1.06  
% 3.89/1.06  ------ Combination Options
% 3.89/1.06  
% 3.89/1.06  --comb_res_mult                         3
% 3.89/1.06  --comb_sup_mult                         2
% 3.89/1.06  --comb_inst_mult                        10
% 3.89/1.06  
% 3.89/1.06  ------ Debug Options
% 3.89/1.06  
% 3.89/1.06  --dbg_backtrace                         false
% 3.89/1.06  --dbg_dump_prop_clauses                 false
% 3.89/1.06  --dbg_dump_prop_clauses_file            -
% 3.89/1.06  --dbg_out_stat                          false
% 3.89/1.06  
% 3.89/1.06  
% 3.89/1.06  
% 3.89/1.06  
% 3.89/1.06  ------ Proving...
% 3.89/1.06  
% 3.89/1.06  
% 3.89/1.06  % SZS status Theorem for theBenchmark.p
% 3.89/1.06  
% 3.89/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/1.06  
% 3.89/1.06  fof(f1,axiom,(
% 3.89/1.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f21,plain,(
% 3.89/1.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/1.06    inference(nnf_transformation,[],[f1])).
% 3.89/1.06  
% 3.89/1.06  fof(f22,plain,(
% 3.89/1.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/1.06    inference(flattening,[],[f21])).
% 3.89/1.06  
% 3.89/1.06  fof(f32,plain,(
% 3.89/1.06    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.89/1.06    inference(cnf_transformation,[],[f22])).
% 3.89/1.06  
% 3.89/1.06  fof(f60,plain,(
% 3.89/1.06    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.89/1.06    inference(equality_resolution,[],[f32])).
% 3.89/1.06  
% 3.89/1.06  fof(f11,conjecture,(
% 3.89/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f12,negated_conjecture,(
% 3.89/1.06    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 3.89/1.06    inference(negated_conjecture,[],[f11])).
% 3.89/1.06  
% 3.89/1.06  fof(f19,plain,(
% 3.89/1.06    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.89/1.06    inference(ennf_transformation,[],[f12])).
% 3.89/1.06  
% 3.89/1.06  fof(f20,plain,(
% 3.89/1.06    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.89/1.06    inference(flattening,[],[f19])).
% 3.89/1.06  
% 3.89/1.06  fof(f29,plain,(
% 3.89/1.06    ( ! [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(sK3,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 3.89/1.06    introduced(choice_axiom,[])).
% 3.89/1.06  
% 3.89/1.06  fof(f28,plain,(
% 3.89/1.06    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(X2,k3_subset_1(sK1,sK2)) & r1_tarski(sK2,k3_subset_1(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.89/1.06    introduced(choice_axiom,[])).
% 3.89/1.06  
% 3.89/1.06  fof(f30,plain,(
% 3.89/1.06    (~r1_tarski(sK3,k3_subset_1(sK1,sK2)) & r1_tarski(sK2,k3_subset_1(sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.89/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f29,f28])).
% 3.89/1.06  
% 3.89/1.06  fof(f52,plain,(
% 3.89/1.06    r1_tarski(sK2,k3_subset_1(sK1,sK3))),
% 3.89/1.06    inference(cnf_transformation,[],[f30])).
% 3.89/1.06  
% 3.89/1.06  fof(f9,axiom,(
% 3.89/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f18,plain,(
% 3.89/1.06    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.89/1.06    inference(ennf_transformation,[],[f9])).
% 3.89/1.06  
% 3.89/1.06  fof(f48,plain,(
% 3.89/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.89/1.06    inference(cnf_transformation,[],[f18])).
% 3.89/1.06  
% 3.89/1.06  fof(f2,axiom,(
% 3.89/1.06    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f34,plain,(
% 3.89/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.89/1.06    inference(cnf_transformation,[],[f2])).
% 3.89/1.06  
% 3.89/1.06  fof(f59,plain,(
% 3.89/1.06    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.89/1.06    inference(definition_unfolding,[],[f48,f34])).
% 3.89/1.06  
% 3.89/1.06  fof(f51,plain,(
% 3.89/1.06    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.89/1.06    inference(cnf_transformation,[],[f30])).
% 3.89/1.06  
% 3.89/1.06  fof(f3,axiom,(
% 3.89/1.06    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f13,plain,(
% 3.89/1.06    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.89/1.06    inference(ennf_transformation,[],[f3])).
% 3.89/1.06  
% 3.89/1.06  fof(f36,plain,(
% 3.89/1.06    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.89/1.06    inference(cnf_transformation,[],[f13])).
% 3.89/1.06  
% 3.89/1.06  fof(f54,plain,(
% 3.89/1.06    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 3.89/1.06    inference(definition_unfolding,[],[f36,f34])).
% 3.89/1.06  
% 3.89/1.06  fof(f6,axiom,(
% 3.89/1.06    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f15,plain,(
% 3.89/1.06    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.89/1.06    inference(ennf_transformation,[],[f6])).
% 3.89/1.06  
% 3.89/1.06  fof(f16,plain,(
% 3.89/1.06    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 3.89/1.06    inference(flattening,[],[f15])).
% 3.89/1.06  
% 3.89/1.06  fof(f39,plain,(
% 3.89/1.06    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.89/1.06    inference(cnf_transformation,[],[f16])).
% 3.89/1.06  
% 3.89/1.06  fof(f58,plain,(
% 3.89/1.06    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.89/1.06    inference(definition_unfolding,[],[f39,f34])).
% 3.89/1.06  
% 3.89/1.06  fof(f4,axiom,(
% 3.89/1.06    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f37,plain,(
% 3.89/1.06    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.89/1.06    inference(cnf_transformation,[],[f4])).
% 3.89/1.06  
% 3.89/1.06  fof(f56,plain,(
% 3.89/1.06    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.89/1.06    inference(definition_unfolding,[],[f37,f34])).
% 3.89/1.06  
% 3.89/1.06  fof(f33,plain,(
% 3.89/1.06    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.89/1.06    inference(cnf_transformation,[],[f22])).
% 3.89/1.06  
% 3.89/1.06  fof(f31,plain,(
% 3.89/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.89/1.06    inference(cnf_transformation,[],[f22])).
% 3.89/1.06  
% 3.89/1.06  fof(f61,plain,(
% 3.89/1.06    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.89/1.06    inference(equality_resolution,[],[f31])).
% 3.89/1.06  
% 3.89/1.06  fof(f5,axiom,(
% 3.89/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f14,plain,(
% 3.89/1.06    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.89/1.06    inference(ennf_transformation,[],[f5])).
% 3.89/1.06  
% 3.89/1.06  fof(f38,plain,(
% 3.89/1.06    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.89/1.06    inference(cnf_transformation,[],[f14])).
% 3.89/1.06  
% 3.89/1.06  fof(f57,plain,(
% 3.89/1.06    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.89/1.06    inference(definition_unfolding,[],[f38,f34])).
% 3.89/1.06  
% 3.89/1.06  fof(f50,plain,(
% 3.89/1.06    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.89/1.06    inference(cnf_transformation,[],[f30])).
% 3.89/1.06  
% 3.89/1.06  fof(f53,plain,(
% 3.89/1.06    ~r1_tarski(sK3,k3_subset_1(sK1,sK2))),
% 3.89/1.06    inference(cnf_transformation,[],[f30])).
% 3.89/1.06  
% 3.89/1.06  fof(f7,axiom,(
% 3.89/1.06    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f23,plain,(
% 3.89/1.06    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.89/1.06    inference(nnf_transformation,[],[f7])).
% 3.89/1.06  
% 3.89/1.06  fof(f24,plain,(
% 3.89/1.06    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.89/1.06    inference(rectify,[],[f23])).
% 3.89/1.06  
% 3.89/1.06  fof(f25,plain,(
% 3.89/1.06    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.89/1.06    introduced(choice_axiom,[])).
% 3.89/1.06  
% 3.89/1.06  fof(f26,plain,(
% 3.89/1.06    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.89/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.89/1.06  
% 3.89/1.06  fof(f40,plain,(
% 3.89/1.06    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.89/1.06    inference(cnf_transformation,[],[f26])).
% 3.89/1.06  
% 3.89/1.06  fof(f63,plain,(
% 3.89/1.06    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.89/1.06    inference(equality_resolution,[],[f40])).
% 3.89/1.06  
% 3.89/1.06  fof(f8,axiom,(
% 3.89/1.06    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f17,plain,(
% 3.89/1.06    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.89/1.06    inference(ennf_transformation,[],[f8])).
% 3.89/1.06  
% 3.89/1.06  fof(f27,plain,(
% 3.89/1.06    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.89/1.06    inference(nnf_transformation,[],[f17])).
% 3.89/1.06  
% 3.89/1.06  fof(f44,plain,(
% 3.89/1.06    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.89/1.06    inference(cnf_transformation,[],[f27])).
% 3.89/1.06  
% 3.89/1.06  fof(f10,axiom,(
% 3.89/1.06    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.89/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/1.06  
% 3.89/1.06  fof(f49,plain,(
% 3.89/1.06    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.89/1.06    inference(cnf_transformation,[],[f10])).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1,plain,
% 3.89/1.06      ( r1_tarski(X0,X0) ),
% 3.89/1.06      inference(cnf_transformation,[],[f60]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1311,plain,
% 3.89/1.06      ( r1_tarski(X0,X0) = iProver_top ),
% 3.89/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_19,negated_conjecture,
% 3.89/1.06      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) ),
% 3.89/1.06      inference(cnf_transformation,[],[f52]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1300,plain,
% 3.89/1.06      ( r1_tarski(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 3.89/1.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_16,plain,
% 3.89/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.89/1.06      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.89/1.06      inference(cnf_transformation,[],[f59]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_20,negated_conjecture,
% 3.89/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.89/1.06      inference(cnf_transformation,[],[f51]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_495,plain,
% 3.89/1.06      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.89/1.06      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.89/1.06      | sK3 != X1 ),
% 3.89/1.06      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_496,plain,
% 3.89/1.06      ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
% 3.89/1.06      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.89/1.06      inference(unflattening,[status(thm)],[c_495]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1475,plain,
% 3.89/1.06      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
% 3.89/1.06      inference(equality_resolution,[status(thm)],[c_496]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_3,plain,
% 3.89/1.06      ( r1_xboole_0(X0,X1)
% 3.89/1.06      | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.89/1.06      inference(cnf_transformation,[],[f54]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1310,plain,
% 3.89/1.06      ( r1_xboole_0(X0,X1) = iProver_top
% 3.89/1.06      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.89/1.06      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_2788,plain,
% 3.89/1.06      ( r1_xboole_0(X0,sK3) = iProver_top
% 3.89/1.06      | r1_tarski(X0,k3_subset_1(sK1,sK3)) != iProver_top ),
% 3.89/1.06      inference(superposition,[status(thm)],[c_1475,c_1310]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_3320,plain,
% 3.89/1.06      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 3.89/1.06      inference(superposition,[status(thm)],[c_1300,c_2788]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_7,plain,
% 3.89/1.06      ( ~ r1_xboole_0(X0,X1)
% 3.89/1.06      | ~ r1_tarski(X0,X2)
% 3.89/1.06      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.89/1.06      inference(cnf_transformation,[],[f58]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1306,plain,
% 3.89/1.06      ( r1_xboole_0(X0,X1) != iProver_top
% 3.89/1.06      | r1_tarski(X0,X2) != iProver_top
% 3.89/1.06      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
% 3.89/1.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_5,plain,
% 3.89/1.06      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.89/1.06      inference(cnf_transformation,[],[f56]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1308,plain,
% 3.89/1.06      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.89/1.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_0,plain,
% 3.89/1.06      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.89/1.06      inference(cnf_transformation,[],[f33]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1312,plain,
% 3.89/1.06      ( X0 = X1
% 3.89/1.06      | r1_tarski(X0,X1) != iProver_top
% 3.89/1.06      | r1_tarski(X1,X0) != iProver_top ),
% 3.89/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_2819,plain,
% 3.89/1.06      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 3.89/1.06      | r1_tarski(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) != iProver_top ),
% 3.89/1.06      inference(superposition,[status(thm)],[c_1308,c_1312]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_10233,plain,
% 3.89/1.06      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 3.89/1.06      | r1_xboole_0(X0,X1) != iProver_top
% 3.89/1.06      | r1_tarski(X0,X0) != iProver_top ),
% 3.89/1.06      inference(superposition,[status(thm)],[c_1306,c_2819]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_2,plain,
% 3.89/1.06      ( r1_tarski(X0,X0) ),
% 3.89/1.06      inference(cnf_transformation,[],[f61]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_69,plain,
% 3.89/1.06      ( r1_tarski(X0,X0) = iProver_top ),
% 3.89/1.06      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_12493,plain,
% 3.89/1.06      ( r1_xboole_0(X0,X1) != iProver_top
% 3.89/1.06      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 3.89/1.06      inference(global_propositional_subsumption,
% 3.89/1.06                [status(thm)],
% 3.89/1.06                [c_10233,c_69]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_12494,plain,
% 3.89/1.06      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 3.89/1.06      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.89/1.06      inference(renaming,[status(thm)],[c_12493]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_12510,plain,
% 3.89/1.06      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = sK2 ),
% 3.89/1.06      inference(superposition,[status(thm)],[c_3320,c_12494]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_6,plain,
% 3.89/1.06      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 3.89/1.06      | ~ r1_tarski(X0,X2) ),
% 3.89/1.06      inference(cnf_transformation,[],[f57]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1307,plain,
% 3.89/1.06      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
% 3.89/1.06      | r1_tarski(X0,X2) != iProver_top ),
% 3.89/1.06      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_13205,plain,
% 3.89/1.06      ( r1_xboole_0(X0,sK2) = iProver_top
% 3.89/1.06      | r1_tarski(X0,sK3) != iProver_top ),
% 3.89/1.06      inference(superposition,[status(thm)],[c_12510,c_1307]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_13839,plain,
% 3.89/1.06      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 3.89/1.06      inference(superposition,[status(thm)],[c_1311,c_13205]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_21,negated_conjecture,
% 3.89/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.89/1.06      inference(cnf_transformation,[],[f50]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_504,plain,
% 3.89/1.06      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.89/1.06      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.89/1.06      | sK2 != X1 ),
% 3.89/1.06      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_505,plain,
% 3.89/1.06      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
% 3.89/1.06      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.89/1.06      inference(unflattening,[status(thm)],[c_504]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1476,plain,
% 3.89/1.06      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 3.89/1.06      inference(equality_resolution,[status(thm)],[c_505]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_3616,plain,
% 3.89/1.06      ( r1_xboole_0(X0,sK2) != iProver_top
% 3.89/1.06      | r1_tarski(X0,k3_subset_1(sK1,sK2)) = iProver_top
% 3.89/1.06      | r1_tarski(X0,sK1) != iProver_top ),
% 3.89/1.06      inference(superposition,[status(thm)],[c_1476,c_1306]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_18,negated_conjecture,
% 3.89/1.06      ( ~ r1_tarski(sK3,k3_subset_1(sK1,sK2)) ),
% 3.89/1.06      inference(cnf_transformation,[],[f53]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_1301,plain,
% 3.89/1.06      ( r1_tarski(sK3,k3_subset_1(sK1,sK2)) != iProver_top ),
% 3.89/1.06      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_4257,plain,
% 3.89/1.06      ( r1_xboole_0(sK3,sK2) != iProver_top
% 3.89/1.06      | r1_tarski(sK3,sK1) != iProver_top ),
% 3.89/1.06      inference(superposition,[status(thm)],[c_3616,c_1301]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_926,plain,
% 3.89/1.06      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.89/1.06      theory(equality) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_933,plain,
% 3.89/1.06      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 3.89/1.06      inference(instantiation,[status(thm)],[c_926]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_11,plain,
% 3.89/1.06      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.89/1.06      inference(cnf_transformation,[],[f63]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_169,plain,
% 3.89/1.06      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.89/1.06      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_170,plain,
% 3.89/1.06      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.89/1.06      inference(renaming,[status(thm)],[c_169]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_15,plain,
% 3.89/1.06      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.89/1.06      inference(cnf_transformation,[],[f44]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_459,plain,
% 3.89/1.06      ( r2_hidden(X0,X1)
% 3.89/1.06      | v1_xboole_0(X1)
% 3.89/1.06      | k1_zfmisc_1(sK1) != X1
% 3.89/1.06      | sK3 != X0 ),
% 3.89/1.06      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_460,plain,
% 3.89/1.06      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.89/1.06      inference(unflattening,[status(thm)],[c_459]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_17,plain,
% 3.89/1.06      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.89/1.06      inference(cnf_transformation,[],[f49]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_27,plain,
% 3.89/1.06      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.89/1.06      inference(instantiation,[status(thm)],[c_17]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_462,plain,
% 3.89/1.06      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 3.89/1.06      inference(global_propositional_subsumption,
% 3.89/1.06                [status(thm)],
% 3.89/1.06                [c_460,c_27]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_604,plain,
% 3.89/1.06      ( r1_tarski(X0,X1)
% 3.89/1.06      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 3.89/1.06      | sK3 != X0 ),
% 3.89/1.06      inference(resolution_lifted,[status(thm)],[c_170,c_462]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_605,plain,
% 3.89/1.06      ( r1_tarski(sK3,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 3.89/1.06      inference(unflattening,[status(thm)],[c_604]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_606,plain,
% 3.89/1.06      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 3.89/1.06      | r1_tarski(sK3,X0) = iProver_top ),
% 3.89/1.06      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_608,plain,
% 3.89/1.06      ( k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1)
% 3.89/1.06      | r1_tarski(sK3,sK1) = iProver_top ),
% 3.89/1.06      inference(instantiation,[status(thm)],[c_606]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_74,plain,
% 3.89/1.06      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.89/1.06      inference(instantiation,[status(thm)],[c_0]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(c_70,plain,
% 3.89/1.06      ( r1_tarski(sK1,sK1) ),
% 3.89/1.06      inference(instantiation,[status(thm)],[c_2]) ).
% 3.89/1.06  
% 3.89/1.06  cnf(contradiction,plain,
% 3.89/1.06      ( $false ),
% 3.89/1.06      inference(minisat,
% 3.89/1.06                [status(thm)],
% 3.89/1.06                [c_13839,c_4257,c_933,c_608,c_74,c_70]) ).
% 3.89/1.06  
% 3.89/1.06  
% 3.89/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/1.06  
% 3.89/1.06  ------                               Statistics
% 3.89/1.06  
% 3.89/1.06  ------ General
% 3.89/1.06  
% 3.89/1.06  abstr_ref_over_cycles:                  0
% 3.89/1.06  abstr_ref_under_cycles:                 0
% 3.89/1.06  gc_basic_clause_elim:                   0
% 3.89/1.06  forced_gc_time:                         0
% 3.89/1.06  parsing_time:                           0.011
% 3.89/1.06  unif_index_cands_time:                  0.
% 3.89/1.06  unif_index_add_time:                    0.
% 3.89/1.06  orderings_time:                         0.
% 3.89/1.06  out_proof_time:                         0.008
% 3.89/1.06  total_time:                             0.478
% 3.89/1.06  num_of_symbols:                         44
% 3.89/1.06  num_of_terms:                           16882
% 3.89/1.06  
% 3.89/1.06  ------ Preprocessing
% 3.89/1.06  
% 3.89/1.06  num_of_splits:                          0
% 3.89/1.06  num_of_split_atoms:                     0
% 3.89/1.06  num_of_reused_defs:                     0
% 3.89/1.06  num_eq_ax_congr_red:                    16
% 3.89/1.06  num_of_sem_filtered_clauses:            1
% 3.89/1.06  num_of_subtypes:                        0
% 3.89/1.06  monotx_restored_types:                  0
% 3.89/1.06  sat_num_of_epr_types:                   0
% 3.89/1.06  sat_num_of_non_cyclic_types:            0
% 3.89/1.06  sat_guarded_non_collapsed_types:        0
% 3.89/1.06  num_pure_diseq_elim:                    0
% 3.89/1.06  simp_replaced_by:                       0
% 3.89/1.06  res_preprocessed:                       94
% 3.89/1.06  prep_upred:                             0
% 3.89/1.06  prep_unflattend:                        50
% 3.89/1.06  smt_new_axioms:                         0
% 3.89/1.06  pred_elim_cands:                        3
% 3.89/1.06  pred_elim:                              2
% 3.89/1.06  pred_elim_cl:                           3
% 3.89/1.06  pred_elim_cycles:                       7
% 3.89/1.06  merged_defs:                            8
% 3.89/1.06  merged_defs_ncl:                        0
% 3.89/1.06  bin_hyper_res:                          9
% 3.89/1.06  prep_cycles:                            4
% 3.89/1.06  pred_elim_time:                         0.01
% 3.89/1.06  splitting_time:                         0.
% 3.89/1.06  sem_filter_time:                        0.
% 3.89/1.06  monotx_time:                            0.001
% 3.89/1.06  subtype_inf_time:                       0.
% 3.89/1.06  
% 3.89/1.06  ------ Problem properties
% 3.89/1.06  
% 3.89/1.06  clauses:                                18
% 3.89/1.06  conjectures:                            2
% 3.89/1.06  epr:                                    2
% 3.89/1.06  horn:                                   17
% 3.89/1.06  ground:                                 4
% 3.89/1.06  unary:                                  6
% 3.89/1.06  binary:                                 8
% 3.89/1.06  lits:                                   34
% 3.89/1.06  lits_eq:                                8
% 3.89/1.06  fd_pure:                                0
% 3.89/1.06  fd_pseudo:                              0
% 3.89/1.06  fd_cond:                                0
% 3.89/1.06  fd_pseudo_cond:                         3
% 3.89/1.06  ac_symbols:                             0
% 3.89/1.06  
% 3.89/1.06  ------ Propositional Solver
% 3.89/1.06  
% 3.89/1.06  prop_solver_calls:                      31
% 3.89/1.06  prop_fast_solver_calls:                 752
% 3.89/1.06  smt_solver_calls:                       0
% 3.89/1.06  smt_fast_solver_calls:                  0
% 3.89/1.06  prop_num_of_clauses:                    6383
% 3.89/1.06  prop_preprocess_simplified:             12191
% 3.89/1.06  prop_fo_subsumed:                       11
% 3.89/1.06  prop_solver_time:                       0.
% 3.89/1.06  smt_solver_time:                        0.
% 3.89/1.06  smt_fast_solver_time:                   0.
% 3.89/1.06  prop_fast_solver_time:                  0.
% 3.89/1.06  prop_unsat_core_time:                   0.
% 3.89/1.06  
% 3.89/1.06  ------ QBF
% 3.89/1.06  
% 3.89/1.06  qbf_q_res:                              0
% 3.89/1.06  qbf_num_tautologies:                    0
% 3.89/1.06  qbf_prep_cycles:                        0
% 3.89/1.06  
% 3.89/1.06  ------ BMC1
% 3.89/1.06  
% 3.89/1.06  bmc1_current_bound:                     -1
% 3.89/1.06  bmc1_last_solved_bound:                 -1
% 3.89/1.06  bmc1_unsat_core_size:                   -1
% 3.89/1.06  bmc1_unsat_core_parents_size:           -1
% 3.89/1.06  bmc1_merge_next_fun:                    0
% 3.89/1.06  bmc1_unsat_core_clauses_time:           0.
% 3.89/1.06  
% 3.89/1.06  ------ Instantiation
% 3.89/1.06  
% 3.89/1.06  inst_num_of_clauses:                    1447
% 3.89/1.06  inst_num_in_passive:                    524
% 3.89/1.06  inst_num_in_active:                     718
% 3.89/1.06  inst_num_in_unprocessed:                205
% 3.89/1.06  inst_num_of_loops:                      830
% 3.89/1.06  inst_num_of_learning_restarts:          0
% 3.89/1.06  inst_num_moves_active_passive:          110
% 3.89/1.06  inst_lit_activity:                      0
% 3.89/1.06  inst_lit_activity_moves:                0
% 3.89/1.06  inst_num_tautologies:                   0
% 3.89/1.06  inst_num_prop_implied:                  0
% 3.89/1.06  inst_num_existing_simplified:           0
% 3.89/1.06  inst_num_eq_res_simplified:             0
% 3.89/1.06  inst_num_child_elim:                    0
% 3.89/1.06  inst_num_of_dismatching_blockings:      1158
% 3.89/1.06  inst_num_of_non_proper_insts:           2189
% 3.89/1.06  inst_num_of_duplicates:                 0
% 3.89/1.06  inst_inst_num_from_inst_to_res:         0
% 3.89/1.06  inst_dismatching_checking_time:         0.
% 3.89/1.06  
% 3.89/1.06  ------ Resolution
% 3.89/1.06  
% 3.89/1.06  res_num_of_clauses:                     0
% 3.89/1.06  res_num_in_passive:                     0
% 3.89/1.06  res_num_in_active:                      0
% 3.89/1.06  res_num_of_loops:                       98
% 3.89/1.06  res_forward_subset_subsumed:            137
% 3.89/1.06  res_backward_subset_subsumed:           6
% 3.89/1.06  res_forward_subsumed:                   3
% 3.89/1.06  res_backward_subsumed:                  0
% 3.89/1.06  res_forward_subsumption_resolution:     2
% 3.89/1.06  res_backward_subsumption_resolution:    0
% 3.89/1.06  res_clause_to_clause_subsumption:       2449
% 3.89/1.06  res_orphan_elimination:                 0
% 3.89/1.06  res_tautology_del:                      189
% 3.89/1.06  res_num_eq_res_simplified:              0
% 3.89/1.06  res_num_sel_changes:                    0
% 3.89/1.06  res_moves_from_active_to_pass:          0
% 3.89/1.06  
% 3.89/1.06  ------ Superposition
% 3.89/1.06  
% 3.89/1.06  sup_time_total:                         0.
% 3.89/1.06  sup_time_generating:                    0.
% 3.89/1.06  sup_time_sim_full:                      0.
% 3.89/1.06  sup_time_sim_immed:                     0.
% 3.89/1.06  
% 3.89/1.06  sup_num_of_clauses:                     630
% 3.89/1.06  sup_num_in_active:                      164
% 3.89/1.06  sup_num_in_passive:                     466
% 3.89/1.06  sup_num_of_loops:                       164
% 3.89/1.06  sup_fw_superposition:                   618
% 3.89/1.06  sup_bw_superposition:                   511
% 3.89/1.06  sup_immediate_simplified:               157
% 3.89/1.06  sup_given_eliminated:                   0
% 3.89/1.06  comparisons_done:                       0
% 3.89/1.06  comparisons_avoided:                    2
% 3.89/1.06  
% 3.89/1.06  ------ Simplifications
% 3.89/1.06  
% 3.89/1.06  
% 3.89/1.06  sim_fw_subset_subsumed:                 19
% 3.89/1.06  sim_bw_subset_subsumed:                 3
% 3.89/1.06  sim_fw_subsumed:                        26
% 3.89/1.06  sim_bw_subsumed:                        0
% 3.89/1.06  sim_fw_subsumption_res:                 0
% 3.89/1.06  sim_bw_subsumption_res:                 0
% 3.89/1.06  sim_tautology_del:                      26
% 3.89/1.06  sim_eq_tautology_del:                   32
% 3.89/1.06  sim_eq_res_simp:                        0
% 3.89/1.06  sim_fw_demodulated:                     69
% 3.89/1.06  sim_bw_demodulated:                     0
% 3.89/1.06  sim_light_normalised:                   42
% 3.89/1.06  sim_joinable_taut:                      0
% 3.89/1.06  sim_joinable_simp:                      0
% 3.89/1.06  sim_ac_normalised:                      0
% 3.89/1.06  sim_smt_subsumption:                    0
% 3.89/1.06  
%------------------------------------------------------------------------------
