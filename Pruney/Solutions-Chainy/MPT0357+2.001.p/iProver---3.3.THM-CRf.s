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
% DateTime   : Thu Dec  3 11:39:45 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  215 (5404 expanded)
%              Number of clauses        :  152 (1758 expanded)
%              Number of leaves         :   23 (1387 expanded)
%              Depth                    :   38
%              Number of atoms          :  380 (13281 expanded)
%              Number of equality atoms :  203 (4074 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f40,f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f41,f40,f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,sK3),X1)
        & r1_tarski(k3_subset_1(X0,X1),sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK1,X2),sK2)
          & r1_tarski(k3_subset_1(sK1,sK2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),sK2)
    & r1_tarski(k3_subset_1(sK1,sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f30,f29])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    r1_tarski(k3_subset_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f62,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f37,f59,f59])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f35,f59])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f42,f43,f43])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f39,f59])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ~ r1_tarski(k3_subset_1(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2568,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_398,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_399,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_405,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_399,c_19])).

cnf(c_1584,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1587,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2379,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1584,c_1587])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1593,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3778,plain,
    ( k4_xboole_0(sK3,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2379,c_1593])).

cnf(c_4148,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3778,c_0])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4149,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_4148,c_6])).

cnf(c_4144,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_3778,c_8])).

cnf(c_4151,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_4144,c_6])).

cnf(c_5851,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_4149,c_4151])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_433,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_434,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_1738,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_434])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1585,plain,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1802,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1738,c_1585])).

cnf(c_3780,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1802,c_1593])).

cnf(c_5,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4043,plain,
    ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k4_xboole_0(sK1,sK2))) = k3_tarski(k2_enumset1(sK3,sK3,sK3,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3780,c_5])).

cnf(c_3,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4046,plain,
    ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k4_xboole_0(sK1,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_4043,c_3])).

cnf(c_9,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_7,plain,
    ( k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2442,plain,
    ( k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_9,c_7])).

cnf(c_4401,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),sK3) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_4046,c_2442])).

cnf(c_4402,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4401,c_3780])).

cnf(c_5871,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_5851,c_4402])).

cnf(c_5872,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_5871,c_6])).

cnf(c_5973,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,sK3),X0))) = k4_xboole_0(k4_xboole_0(sK3,sK3),X0) ),
    inference(superposition,[status(thm)],[c_5872,c_8])).

cnf(c_2066,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_3])).

cnf(c_2441,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2066,c_7])).

cnf(c_2617,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2441,c_5])).

cnf(c_2622,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2617,c_3])).

cnf(c_3903,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2622,c_2442])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1591,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2251,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1591])).

cnf(c_3782,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2251,c_1593])).

cnf(c_3918,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3903,c_3782])).

cnf(c_5978,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,sK3),X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5973,c_3918,c_4402])).

cnf(c_4407,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_4402,c_8])).

cnf(c_4426,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_4407,c_6])).

cnf(c_7402,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5978,c_4426])).

cnf(c_7709,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_7402,c_6])).

cnf(c_4040,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_3780,c_8])).

cnf(c_4047,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_4040,c_6])).

cnf(c_8142,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)) ),
    inference(superposition,[status(thm)],[c_7709,c_4047])).

cnf(c_8144,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_8142,c_3780])).

cnf(c_8145,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_8144,c_6])).

cnf(c_5261,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK3,X0),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X0),X1) ),
    inference(superposition,[status(thm)],[c_4047,c_8])).

cnf(c_8127,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK3)))) = sK3 ),
    inference(superposition,[status(thm)],[c_0,c_7709])).

cnf(c_2249,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1591])).

cnf(c_2907,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2249])).

cnf(c_2916,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2907,c_8])).

cnf(c_13605,plain,
    ( r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(sK3,sK3)))),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8127,c_2916])).

cnf(c_7401,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_4151,c_4426])).

cnf(c_13766,plain,
    ( r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK1,X0)),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13605,c_6,c_4402,c_7401])).

cnf(c_14394,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK1,X0)),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13766,c_1593])).

cnf(c_14835,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0)),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_14394,c_5261])).

cnf(c_5863,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,k4_xboole_0(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_4151,c_4047])).

cnf(c_5865,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_5863,c_4047])).

cnf(c_7992,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_5865,c_4047])).

cnf(c_9145,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_7992,c_8])).

cnf(c_9171,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_9145,c_7992])).

cnf(c_7399,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4426])).

cnf(c_9848,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,sK3))) ),
    inference(superposition,[status(thm)],[c_7399,c_4047])).

cnf(c_9856,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_9848,c_4047])).

cnf(c_10216,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_4149,c_9856])).

cnf(c_10290,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10216,c_3780])).

cnf(c_14836,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0)),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14835,c_6,c_7992,c_9171,c_10290])).

cnf(c_14938,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK1,sK3))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_14836])).

cnf(c_17791,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X0),k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5261,c_14938])).

cnf(c_9153,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_7992,c_7992])).

cnf(c_9165,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) ),
    inference(demodulation,[status(thm)],[c_9153,c_7992])).

cnf(c_4147,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3778,c_5])).

cnf(c_4150,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4147,c_3])).

cnf(c_4768,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_4150,c_2442])).

cnf(c_4769,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4768,c_3778])).

cnf(c_5413,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_4769,c_8])).

cnf(c_5432,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_5413,c_6])).

cnf(c_8524,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,k4_xboole_0(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_5432,c_5865])).

cnf(c_8530,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_8524,c_5865])).

cnf(c_9166,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_9165,c_8530])).

cnf(c_17984,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X0),k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17791,c_4047,c_9166])).

cnf(c_19394,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_17984])).

cnf(c_2580,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1591])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_377,plain,
    ( ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X2 != X0
    | k3_subset_1(X3,X2) = k4_xboole_0(X3,X2)
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_378,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_149,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_150,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_149])).

cnf(c_321,plain,
    ( m1_subset_1(X0,X1)
    | ~ r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | X0 != X2
    | k1_zfmisc_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_150,c_16])).

cnf(c_322,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_332,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_322,c_19])).

cnf(c_382,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_18,c_13,c_332])).

cnf(c_845,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_846,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_845])).

cnf(c_878,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_382,c_846])).

cnf(c_1582,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_878])).

cnf(c_6575,plain,
    ( k3_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_2580,c_1582])).

cnf(c_2252,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1591,c_1582])).

cnf(c_5519,plain,
    ( k3_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_8,c_2252])).

cnf(c_5571,plain,
    ( k3_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_5519,c_8])).

cnf(c_5572,plain,
    ( k3_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) ),
    inference(demodulation,[status(thm)],[c_5571,c_8])).

cnf(c_6576,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_6575,c_5572])).

cnf(c_19507,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19394,c_8,c_6576])).

cnf(c_5975,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_5872,c_4047])).

cnf(c_5976,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_5975,c_3780])).

cnf(c_5977,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_5976,c_6])).

cnf(c_9124,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) ),
    inference(superposition,[status(thm)],[c_0,c_7992])).

cnf(c_9193,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_9124,c_9166])).

cnf(c_19508,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_19507,c_5977,c_9193])).

cnf(c_19597,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK3),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK3),X0),k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8145,c_19508])).

cnf(c_34366,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK3),X0))),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2568,c_19597])).

cnf(c_4628,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK3),X0))) = k4_xboole_0(k4_xboole_0(sK1,sK3),X0) ),
    inference(superposition,[status(thm)],[c_4149,c_8])).

cnf(c_34860,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK3),X0),sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_34366,c_4628])).

cnf(c_35385,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0),sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_34860])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1838,plain,
    ( r1_tarski(X0,sK2)
    | k4_xboole_0(X0,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_11309,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0),sK2)
    | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0),sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_1265,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1616,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK1,sK3),sK2)
    | k3_subset_1(sK1,sK3) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_1654,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k3_subset_1(sK1,sK3),sK2)
    | k3_subset_1(sK1,sK3) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_7857,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),sK2)
    | ~ r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0),sK2)
    | k3_subset_1(sK1,sK3) != k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1654])).

cnf(c_3146,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k4_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1263,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1943,plain,
    ( X0 != X1
    | k3_subset_1(sK1,sK3) != X1
    | k3_subset_1(sK1,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_2163,plain,
    ( X0 != k4_xboole_0(sK1,sK3)
    | k3_subset_1(sK1,sK3) = X0
    | k3_subset_1(sK1,sK3) != k4_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1943])).

cnf(c_2189,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)
    | k3_subset_1(sK1,sK3) != k4_xboole_0(sK1,sK3)
    | k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) != k4_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_2163])).

cnf(c_1262,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1709,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_1662,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_424,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_425,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_1631,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35385,c_11309,c_7857,c_3146,c_2189,c_1709,c_1662,c_1631,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 11.65/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.65/1.98  
% 11.65/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.65/1.98  
% 11.65/1.98  ------  iProver source info
% 11.65/1.98  
% 11.65/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.65/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.65/1.98  git: non_committed_changes: false
% 11.65/1.98  git: last_make_outside_of_git: false
% 11.65/1.98  
% 11.65/1.98  ------ 
% 11.65/1.98  
% 11.65/1.98  ------ Input Options
% 11.65/1.98  
% 11.65/1.98  --out_options                           all
% 11.65/1.98  --tptp_safe_out                         true
% 11.65/1.98  --problem_path                          ""
% 11.65/1.98  --include_path                          ""
% 11.65/1.98  --clausifier                            res/vclausify_rel
% 11.65/1.98  --clausifier_options                    ""
% 11.65/1.98  --stdin                                 false
% 11.65/1.98  --stats_out                             all
% 11.65/1.98  
% 11.65/1.98  ------ General Options
% 11.65/1.98  
% 11.65/1.98  --fof                                   false
% 11.65/1.98  --time_out_real                         305.
% 11.65/1.98  --time_out_virtual                      -1.
% 11.65/1.98  --symbol_type_check                     false
% 11.65/1.98  --clausify_out                          false
% 11.65/1.98  --sig_cnt_out                           false
% 11.65/1.98  --trig_cnt_out                          false
% 11.65/1.98  --trig_cnt_out_tolerance                1.
% 11.65/1.98  --trig_cnt_out_sk_spl                   false
% 11.65/1.98  --abstr_cl_out                          false
% 11.65/1.98  
% 11.65/1.98  ------ Global Options
% 11.65/1.98  
% 11.65/1.98  --schedule                              default
% 11.65/1.98  --add_important_lit                     false
% 11.65/1.98  --prop_solver_per_cl                    1000
% 11.65/1.98  --min_unsat_core                        false
% 11.65/1.98  --soft_assumptions                      false
% 11.65/1.98  --soft_lemma_size                       3
% 11.65/1.98  --prop_impl_unit_size                   0
% 11.65/1.98  --prop_impl_unit                        []
% 11.65/1.98  --share_sel_clauses                     true
% 11.65/1.98  --reset_solvers                         false
% 11.65/1.98  --bc_imp_inh                            [conj_cone]
% 11.65/1.98  --conj_cone_tolerance                   3.
% 11.65/1.98  --extra_neg_conj                        none
% 11.65/1.98  --large_theory_mode                     true
% 11.65/1.98  --prolific_symb_bound                   200
% 11.65/1.98  --lt_threshold                          2000
% 11.65/1.98  --clause_weak_htbl                      true
% 11.65/1.98  --gc_record_bc_elim                     false
% 11.65/1.98  
% 11.65/1.98  ------ Preprocessing Options
% 11.65/1.98  
% 11.65/1.98  --preprocessing_flag                    true
% 11.65/1.98  --time_out_prep_mult                    0.1
% 11.65/1.98  --splitting_mode                        input
% 11.65/1.98  --splitting_grd                         true
% 11.65/1.98  --splitting_cvd                         false
% 11.65/1.98  --splitting_cvd_svl                     false
% 11.65/1.98  --splitting_nvd                         32
% 11.65/1.98  --sub_typing                            true
% 11.65/1.98  --prep_gs_sim                           true
% 11.65/1.98  --prep_unflatten                        true
% 11.65/1.98  --prep_res_sim                          true
% 11.65/1.98  --prep_upred                            true
% 11.65/1.98  --prep_sem_filter                       exhaustive
% 11.65/1.98  --prep_sem_filter_out                   false
% 11.65/1.98  --pred_elim                             true
% 11.65/1.98  --res_sim_input                         true
% 11.65/1.98  --eq_ax_congr_red                       true
% 11.65/1.98  --pure_diseq_elim                       true
% 11.65/1.98  --brand_transform                       false
% 11.65/1.98  --non_eq_to_eq                          false
% 11.65/1.98  --prep_def_merge                        true
% 11.65/1.98  --prep_def_merge_prop_impl              false
% 11.65/1.98  --prep_def_merge_mbd                    true
% 11.65/1.98  --prep_def_merge_tr_red                 false
% 11.65/1.98  --prep_def_merge_tr_cl                  false
% 11.65/1.98  --smt_preprocessing                     true
% 11.65/1.98  --smt_ac_axioms                         fast
% 11.65/1.98  --preprocessed_out                      false
% 11.65/1.98  --preprocessed_stats                    false
% 11.65/1.98  
% 11.65/1.98  ------ Abstraction refinement Options
% 11.65/1.98  
% 11.65/1.98  --abstr_ref                             []
% 11.65/1.98  --abstr_ref_prep                        false
% 11.65/1.98  --abstr_ref_until_sat                   false
% 11.65/1.98  --abstr_ref_sig_restrict                funpre
% 11.65/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/1.98  --abstr_ref_under                       []
% 11.65/1.98  
% 11.65/1.98  ------ SAT Options
% 11.65/1.98  
% 11.65/1.98  --sat_mode                              false
% 11.65/1.98  --sat_fm_restart_options                ""
% 11.65/1.98  --sat_gr_def                            false
% 11.65/1.98  --sat_epr_types                         true
% 11.65/1.98  --sat_non_cyclic_types                  false
% 11.65/1.98  --sat_finite_models                     false
% 11.65/1.98  --sat_fm_lemmas                         false
% 11.65/1.98  --sat_fm_prep                           false
% 11.65/1.98  --sat_fm_uc_incr                        true
% 11.65/1.98  --sat_out_model                         small
% 11.65/1.98  --sat_out_clauses                       false
% 11.65/1.98  
% 11.65/1.98  ------ QBF Options
% 11.65/1.98  
% 11.65/1.98  --qbf_mode                              false
% 11.65/1.98  --qbf_elim_univ                         false
% 11.65/1.98  --qbf_dom_inst                          none
% 11.65/1.98  --qbf_dom_pre_inst                      false
% 11.65/1.98  --qbf_sk_in                             false
% 11.65/1.98  --qbf_pred_elim                         true
% 11.65/1.98  --qbf_split                             512
% 11.65/1.98  
% 11.65/1.98  ------ BMC1 Options
% 11.65/1.98  
% 11.65/1.98  --bmc1_incremental                      false
% 11.65/1.98  --bmc1_axioms                           reachable_all
% 11.65/1.98  --bmc1_min_bound                        0
% 11.65/1.98  --bmc1_max_bound                        -1
% 11.65/1.98  --bmc1_max_bound_default                -1
% 11.65/1.98  --bmc1_symbol_reachability              true
% 11.65/1.98  --bmc1_property_lemmas                  false
% 11.65/1.98  --bmc1_k_induction                      false
% 11.65/1.98  --bmc1_non_equiv_states                 false
% 11.65/1.98  --bmc1_deadlock                         false
% 11.65/1.98  --bmc1_ucm                              false
% 11.65/1.98  --bmc1_add_unsat_core                   none
% 11.65/1.98  --bmc1_unsat_core_children              false
% 11.65/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/1.98  --bmc1_out_stat                         full
% 11.65/1.98  --bmc1_ground_init                      false
% 11.65/1.98  --bmc1_pre_inst_next_state              false
% 11.65/1.98  --bmc1_pre_inst_state                   false
% 11.65/1.98  --bmc1_pre_inst_reach_state             false
% 11.65/1.98  --bmc1_out_unsat_core                   false
% 11.65/1.98  --bmc1_aig_witness_out                  false
% 11.65/1.98  --bmc1_verbose                          false
% 11.65/1.98  --bmc1_dump_clauses_tptp                false
% 11.65/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.65/1.98  --bmc1_dump_file                        -
% 11.65/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.65/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.65/1.98  --bmc1_ucm_extend_mode                  1
% 11.65/1.98  --bmc1_ucm_init_mode                    2
% 11.65/1.98  --bmc1_ucm_cone_mode                    none
% 11.65/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.65/1.98  --bmc1_ucm_relax_model                  4
% 11.65/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.65/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/1.98  --bmc1_ucm_layered_model                none
% 11.65/1.98  --bmc1_ucm_max_lemma_size               10
% 11.65/1.98  
% 11.65/1.98  ------ AIG Options
% 11.65/1.98  
% 11.65/1.98  --aig_mode                              false
% 11.65/1.98  
% 11.65/1.98  ------ Instantiation Options
% 11.65/1.98  
% 11.65/1.98  --instantiation_flag                    true
% 11.65/1.98  --inst_sos_flag                         true
% 11.65/1.98  --inst_sos_phase                        true
% 11.65/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/1.98  --inst_lit_sel_side                     num_symb
% 11.65/1.98  --inst_solver_per_active                1400
% 11.65/1.98  --inst_solver_calls_frac                1.
% 11.65/1.98  --inst_passive_queue_type               priority_queues
% 11.65/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/1.98  --inst_passive_queues_freq              [25;2]
% 11.65/1.98  --inst_dismatching                      true
% 11.65/1.98  --inst_eager_unprocessed_to_passive     true
% 11.65/1.98  --inst_prop_sim_given                   true
% 11.65/1.98  --inst_prop_sim_new                     false
% 11.65/1.98  --inst_subs_new                         false
% 11.65/1.98  --inst_eq_res_simp                      false
% 11.65/1.98  --inst_subs_given                       false
% 11.65/1.98  --inst_orphan_elimination               true
% 11.65/1.98  --inst_learning_loop_flag               true
% 11.65/1.98  --inst_learning_start                   3000
% 11.65/1.98  --inst_learning_factor                  2
% 11.65/1.98  --inst_start_prop_sim_after_learn       3
% 11.65/1.98  --inst_sel_renew                        solver
% 11.65/1.98  --inst_lit_activity_flag                true
% 11.65/1.98  --inst_restr_to_given                   false
% 11.65/1.98  --inst_activity_threshold               500
% 11.65/1.98  --inst_out_proof                        true
% 11.65/1.98  
% 11.65/1.98  ------ Resolution Options
% 11.65/1.98  
% 11.65/1.98  --resolution_flag                       true
% 11.65/1.98  --res_lit_sel                           adaptive
% 11.65/1.98  --res_lit_sel_side                      none
% 11.65/1.98  --res_ordering                          kbo
% 11.65/1.98  --res_to_prop_solver                    active
% 11.65/1.98  --res_prop_simpl_new                    false
% 11.65/1.98  --res_prop_simpl_given                  true
% 11.65/1.98  --res_passive_queue_type                priority_queues
% 11.65/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/1.98  --res_passive_queues_freq               [15;5]
% 11.65/1.98  --res_forward_subs                      full
% 11.65/1.98  --res_backward_subs                     full
% 11.65/1.98  --res_forward_subs_resolution           true
% 11.65/1.98  --res_backward_subs_resolution          true
% 11.65/1.98  --res_orphan_elimination                true
% 11.65/1.98  --res_time_limit                        2.
% 11.65/1.98  --res_out_proof                         true
% 11.65/1.98  
% 11.65/1.98  ------ Superposition Options
% 11.65/1.98  
% 11.65/1.98  --superposition_flag                    true
% 11.65/1.98  --sup_passive_queue_type                priority_queues
% 11.65/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.65/1.98  --demod_completeness_check              fast
% 11.65/1.98  --demod_use_ground                      true
% 11.65/1.98  --sup_to_prop_solver                    passive
% 11.65/1.98  --sup_prop_simpl_new                    true
% 11.65/1.98  --sup_prop_simpl_given                  true
% 11.65/1.98  --sup_fun_splitting                     true
% 11.65/1.98  --sup_smt_interval                      50000
% 11.65/1.98  
% 11.65/1.98  ------ Superposition Simplification Setup
% 11.65/1.98  
% 11.65/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.65/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.65/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.65/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.65/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.65/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.65/1.98  --sup_immed_triv                        [TrivRules]
% 11.65/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.98  --sup_immed_bw_main                     []
% 11.65/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.65/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.98  --sup_input_bw                          []
% 11.65/1.98  
% 11.65/1.98  ------ Combination Options
% 11.65/1.98  
% 11.65/1.98  --comb_res_mult                         3
% 11.65/1.98  --comb_sup_mult                         2
% 11.65/1.98  --comb_inst_mult                        10
% 11.65/1.98  
% 11.65/1.98  ------ Debug Options
% 11.65/1.98  
% 11.65/1.98  --dbg_backtrace                         false
% 11.65/1.98  --dbg_dump_prop_clauses                 false
% 11.65/1.98  --dbg_dump_prop_clauses_file            -
% 11.65/1.98  --dbg_out_stat                          false
% 11.65/1.98  ------ Parsing...
% 11.65/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.65/1.98  
% 11.65/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.65/1.98  
% 11.65/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.65/1.98  
% 11.65/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.65/1.98  ------ Proving...
% 11.65/1.98  ------ Problem Properties 
% 11.65/1.98  
% 11.65/1.98  
% 11.65/1.98  clauses                                 21
% 11.65/1.98  conjectures                             2
% 11.65/1.98  EPR                                     0
% 11.65/1.98  Horn                                    20
% 11.65/1.98  unary                                   12
% 11.65/1.98  binary                                  7
% 11.65/1.98  lits                                    32
% 11.65/1.98  lits eq                                 16
% 11.65/1.98  fd_pure                                 0
% 11.65/1.98  fd_pseudo                               0
% 11.65/1.98  fd_cond                                 0
% 11.65/1.98  fd_pseudo_cond                          2
% 11.65/1.98  AC symbols                              0
% 11.65/1.98  
% 11.65/1.98  ------ Schedule dynamic 5 is on 
% 11.65/1.98  
% 11.65/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.65/1.98  
% 11.65/1.98  
% 11.65/1.98  ------ 
% 11.65/1.98  Current options:
% 11.65/1.98  ------ 
% 11.65/1.98  
% 11.65/1.98  ------ Input Options
% 11.65/1.98  
% 11.65/1.98  --out_options                           all
% 11.65/1.98  --tptp_safe_out                         true
% 11.65/1.98  --problem_path                          ""
% 11.65/1.98  --include_path                          ""
% 11.65/1.98  --clausifier                            res/vclausify_rel
% 11.65/1.98  --clausifier_options                    ""
% 11.65/1.98  --stdin                                 false
% 11.65/1.98  --stats_out                             all
% 11.65/1.98  
% 11.65/1.98  ------ General Options
% 11.65/1.98  
% 11.65/1.98  --fof                                   false
% 11.65/1.98  --time_out_real                         305.
% 11.65/1.98  --time_out_virtual                      -1.
% 11.65/1.98  --symbol_type_check                     false
% 11.65/1.98  --clausify_out                          false
% 11.65/1.98  --sig_cnt_out                           false
% 11.65/1.98  --trig_cnt_out                          false
% 11.65/1.98  --trig_cnt_out_tolerance                1.
% 11.65/1.98  --trig_cnt_out_sk_spl                   false
% 11.65/1.98  --abstr_cl_out                          false
% 11.65/1.98  
% 11.65/1.98  ------ Global Options
% 11.65/1.98  
% 11.65/1.98  --schedule                              default
% 11.65/1.98  --add_important_lit                     false
% 11.65/1.98  --prop_solver_per_cl                    1000
% 11.65/1.98  --min_unsat_core                        false
% 11.65/1.98  --soft_assumptions                      false
% 11.65/1.98  --soft_lemma_size                       3
% 11.65/1.98  --prop_impl_unit_size                   0
% 11.65/1.98  --prop_impl_unit                        []
% 11.65/1.98  --share_sel_clauses                     true
% 11.65/1.98  --reset_solvers                         false
% 11.65/1.98  --bc_imp_inh                            [conj_cone]
% 11.65/1.98  --conj_cone_tolerance                   3.
% 11.65/1.98  --extra_neg_conj                        none
% 11.65/1.98  --large_theory_mode                     true
% 11.65/1.98  --prolific_symb_bound                   200
% 11.65/1.98  --lt_threshold                          2000
% 11.65/1.98  --clause_weak_htbl                      true
% 11.65/1.98  --gc_record_bc_elim                     false
% 11.65/1.98  
% 11.65/1.98  ------ Preprocessing Options
% 11.65/1.98  
% 11.65/1.98  --preprocessing_flag                    true
% 11.65/1.98  --time_out_prep_mult                    0.1
% 11.65/1.98  --splitting_mode                        input
% 11.65/1.98  --splitting_grd                         true
% 11.65/1.98  --splitting_cvd                         false
% 11.65/1.98  --splitting_cvd_svl                     false
% 11.65/1.98  --splitting_nvd                         32
% 11.65/1.98  --sub_typing                            true
% 11.65/1.98  --prep_gs_sim                           true
% 11.65/1.98  --prep_unflatten                        true
% 11.65/1.98  --prep_res_sim                          true
% 11.65/1.98  --prep_upred                            true
% 11.65/1.98  --prep_sem_filter                       exhaustive
% 11.65/1.98  --prep_sem_filter_out                   false
% 11.65/1.98  --pred_elim                             true
% 11.65/1.98  --res_sim_input                         true
% 11.65/1.98  --eq_ax_congr_red                       true
% 11.65/1.98  --pure_diseq_elim                       true
% 11.65/1.98  --brand_transform                       false
% 11.65/1.98  --non_eq_to_eq                          false
% 11.65/1.98  --prep_def_merge                        true
% 11.65/1.98  --prep_def_merge_prop_impl              false
% 11.65/1.98  --prep_def_merge_mbd                    true
% 11.65/1.98  --prep_def_merge_tr_red                 false
% 11.65/1.98  --prep_def_merge_tr_cl                  false
% 11.65/1.98  --smt_preprocessing                     true
% 11.65/1.98  --smt_ac_axioms                         fast
% 11.65/1.98  --preprocessed_out                      false
% 11.65/1.98  --preprocessed_stats                    false
% 11.65/1.98  
% 11.65/1.98  ------ Abstraction refinement Options
% 11.65/1.98  
% 11.65/1.98  --abstr_ref                             []
% 11.65/1.98  --abstr_ref_prep                        false
% 11.65/1.98  --abstr_ref_until_sat                   false
% 11.65/1.98  --abstr_ref_sig_restrict                funpre
% 11.65/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/1.98  --abstr_ref_under                       []
% 11.65/1.98  
% 11.65/1.98  ------ SAT Options
% 11.65/1.98  
% 11.65/1.98  --sat_mode                              false
% 11.65/1.98  --sat_fm_restart_options                ""
% 11.65/1.98  --sat_gr_def                            false
% 11.65/1.98  --sat_epr_types                         true
% 11.65/1.98  --sat_non_cyclic_types                  false
% 11.65/1.98  --sat_finite_models                     false
% 11.65/1.98  --sat_fm_lemmas                         false
% 11.65/1.98  --sat_fm_prep                           false
% 11.65/1.98  --sat_fm_uc_incr                        true
% 11.65/1.98  --sat_out_model                         small
% 11.65/1.98  --sat_out_clauses                       false
% 11.65/1.98  
% 11.65/1.98  ------ QBF Options
% 11.65/1.98  
% 11.65/1.98  --qbf_mode                              false
% 11.65/1.98  --qbf_elim_univ                         false
% 11.65/1.98  --qbf_dom_inst                          none
% 11.65/1.98  --qbf_dom_pre_inst                      false
% 11.65/1.98  --qbf_sk_in                             false
% 11.65/1.98  --qbf_pred_elim                         true
% 11.65/1.98  --qbf_split                             512
% 11.65/1.98  
% 11.65/1.98  ------ BMC1 Options
% 11.65/1.98  
% 11.65/1.98  --bmc1_incremental                      false
% 11.65/1.98  --bmc1_axioms                           reachable_all
% 11.65/1.98  --bmc1_min_bound                        0
% 11.65/1.98  --bmc1_max_bound                        -1
% 11.65/1.98  --bmc1_max_bound_default                -1
% 11.65/1.98  --bmc1_symbol_reachability              true
% 11.65/1.98  --bmc1_property_lemmas                  false
% 11.65/1.98  --bmc1_k_induction                      false
% 11.65/1.98  --bmc1_non_equiv_states                 false
% 11.65/1.98  --bmc1_deadlock                         false
% 11.65/1.98  --bmc1_ucm                              false
% 11.65/1.98  --bmc1_add_unsat_core                   none
% 11.65/1.98  --bmc1_unsat_core_children              false
% 11.65/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/1.98  --bmc1_out_stat                         full
% 11.65/1.98  --bmc1_ground_init                      false
% 11.65/1.98  --bmc1_pre_inst_next_state              false
% 11.65/1.98  --bmc1_pre_inst_state                   false
% 11.65/1.98  --bmc1_pre_inst_reach_state             false
% 11.65/1.98  --bmc1_out_unsat_core                   false
% 11.65/1.98  --bmc1_aig_witness_out                  false
% 11.65/1.98  --bmc1_verbose                          false
% 11.65/1.98  --bmc1_dump_clauses_tptp                false
% 11.65/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.65/1.98  --bmc1_dump_file                        -
% 11.65/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.65/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.65/1.98  --bmc1_ucm_extend_mode                  1
% 11.65/1.98  --bmc1_ucm_init_mode                    2
% 11.65/1.98  --bmc1_ucm_cone_mode                    none
% 11.65/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.65/1.98  --bmc1_ucm_relax_model                  4
% 11.65/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.65/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/1.98  --bmc1_ucm_layered_model                none
% 11.65/1.98  --bmc1_ucm_max_lemma_size               10
% 11.65/1.98  
% 11.65/1.98  ------ AIG Options
% 11.65/1.98  
% 11.65/1.98  --aig_mode                              false
% 11.65/1.98  
% 11.65/1.98  ------ Instantiation Options
% 11.65/1.98  
% 11.65/1.98  --instantiation_flag                    true
% 11.65/1.98  --inst_sos_flag                         true
% 11.65/1.98  --inst_sos_phase                        true
% 11.65/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/1.98  --inst_lit_sel_side                     none
% 11.65/1.98  --inst_solver_per_active                1400
% 11.65/1.98  --inst_solver_calls_frac                1.
% 11.65/1.98  --inst_passive_queue_type               priority_queues
% 11.65/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/1.98  --inst_passive_queues_freq              [25;2]
% 11.65/1.98  --inst_dismatching                      true
% 11.65/1.98  --inst_eager_unprocessed_to_passive     true
% 11.65/1.98  --inst_prop_sim_given                   true
% 11.65/1.98  --inst_prop_sim_new                     false
% 11.65/1.98  --inst_subs_new                         false
% 11.65/1.98  --inst_eq_res_simp                      false
% 11.65/1.98  --inst_subs_given                       false
% 11.65/1.98  --inst_orphan_elimination               true
% 11.65/1.98  --inst_learning_loop_flag               true
% 11.65/1.98  --inst_learning_start                   3000
% 11.65/1.98  --inst_learning_factor                  2
% 11.65/1.98  --inst_start_prop_sim_after_learn       3
% 11.65/1.98  --inst_sel_renew                        solver
% 11.65/1.98  --inst_lit_activity_flag                true
% 11.65/1.98  --inst_restr_to_given                   false
% 11.65/1.98  --inst_activity_threshold               500
% 11.65/1.98  --inst_out_proof                        true
% 11.65/1.98  
% 11.65/1.98  ------ Resolution Options
% 11.65/1.98  
% 11.65/1.98  --resolution_flag                       false
% 11.65/1.98  --res_lit_sel                           adaptive
% 11.65/1.98  --res_lit_sel_side                      none
% 11.65/1.98  --res_ordering                          kbo
% 11.65/1.98  --res_to_prop_solver                    active
% 11.65/1.98  --res_prop_simpl_new                    false
% 11.65/1.98  --res_prop_simpl_given                  true
% 11.65/1.98  --res_passive_queue_type                priority_queues
% 11.65/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/1.98  --res_passive_queues_freq               [15;5]
% 11.65/1.98  --res_forward_subs                      full
% 11.65/1.98  --res_backward_subs                     full
% 11.65/1.98  --res_forward_subs_resolution           true
% 11.65/1.98  --res_backward_subs_resolution          true
% 11.65/1.98  --res_orphan_elimination                true
% 11.65/1.98  --res_time_limit                        2.
% 11.65/1.98  --res_out_proof                         true
% 11.65/1.98  
% 11.65/1.98  ------ Superposition Options
% 11.65/1.98  
% 11.65/1.98  --superposition_flag                    true
% 11.65/1.98  --sup_passive_queue_type                priority_queues
% 11.65/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.65/1.98  --demod_completeness_check              fast
% 11.65/1.98  --demod_use_ground                      true
% 11.65/1.98  --sup_to_prop_solver                    passive
% 11.65/1.98  --sup_prop_simpl_new                    true
% 11.65/1.98  --sup_prop_simpl_given                  true
% 11.65/1.98  --sup_fun_splitting                     true
% 11.65/1.98  --sup_smt_interval                      50000
% 11.65/1.98  
% 11.65/1.98  ------ Superposition Simplification Setup
% 11.65/1.98  
% 11.65/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.65/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.65/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.65/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.65/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.65/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.65/1.98  --sup_immed_triv                        [TrivRules]
% 11.65/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.98  --sup_immed_bw_main                     []
% 11.65/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.65/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/1.98  --sup_input_bw                          []
% 11.65/1.98  
% 11.65/1.98  ------ Combination Options
% 11.65/1.98  
% 11.65/1.98  --comb_res_mult                         3
% 11.65/1.98  --comb_sup_mult                         2
% 11.65/1.98  --comb_inst_mult                        10
% 11.65/1.98  
% 11.65/1.98  ------ Debug Options
% 11.65/1.98  
% 11.65/1.98  --dbg_backtrace                         false
% 11.65/1.98  --dbg_dump_prop_clauses                 false
% 11.65/1.98  --dbg_dump_prop_clauses_file            -
% 11.65/1.98  --dbg_out_stat                          false
% 11.65/1.98  
% 11.65/1.98  
% 11.65/1.98  
% 11.65/1.98  
% 11.65/1.98  ------ Proving...
% 11.65/1.98  
% 11.65/1.98  
% 11.65/1.98  % SZS status Theorem for theBenchmark.p
% 11.65/1.98  
% 11.65/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.65/1.98  
% 11.65/1.98  fof(f1,axiom,(
% 11.65/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f32,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.65/1.98    inference(cnf_transformation,[],[f1])).
% 11.65/1.98  
% 11.65/1.98  fof(f8,axiom,(
% 11.65/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f40,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.65/1.98    inference(cnf_transformation,[],[f8])).
% 11.65/1.98  
% 11.65/1.98  fof(f60,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.65/1.98    inference(definition_unfolding,[],[f32,f40,f40])).
% 11.65/1.98  
% 11.65/1.98  fof(f9,axiom,(
% 11.65/1.98    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f41,plain,(
% 11.65/1.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.65/1.98    inference(cnf_transformation,[],[f9])).
% 11.65/1.98  
% 11.65/1.98  fof(f64,plain,(
% 11.65/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 11.65/1.98    inference(definition_unfolding,[],[f41,f40,f40])).
% 11.65/1.98  
% 11.65/1.98  fof(f14,axiom,(
% 11.65/1.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f19,plain,(
% 11.65/1.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.65/1.98    inference(ennf_transformation,[],[f14])).
% 11.65/1.98  
% 11.65/1.98  fof(f28,plain,(
% 11.65/1.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.65/1.98    inference(nnf_transformation,[],[f19])).
% 11.65/1.98  
% 11.65/1.98  fof(f49,plain,(
% 11.65/1.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.65/1.98    inference(cnf_transformation,[],[f28])).
% 11.65/1.98  
% 11.65/1.98  fof(f17,conjecture,(
% 11.65/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f18,negated_conjecture,(
% 11.65/1.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 11.65/1.98    inference(negated_conjecture,[],[f17])).
% 11.65/1.98  
% 11.65/1.98  fof(f21,plain,(
% 11.65/1.98    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.65/1.98    inference(ennf_transformation,[],[f18])).
% 11.65/1.98  
% 11.65/1.98  fof(f22,plain,(
% 11.65/1.98    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.65/1.98    inference(flattening,[],[f21])).
% 11.65/1.98  
% 11.65/1.98  fof(f30,plain,(
% 11.65/1.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(k3_subset_1(X0,sK3),X1) & r1_tarski(k3_subset_1(X0,X1),sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 11.65/1.98    introduced(choice_axiom,[])).
% 11.65/1.98  
% 11.65/1.98  fof(f29,plain,(
% 11.65/1.98    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,X2),sK2) & r1_tarski(k3_subset_1(sK1,sK2),X2) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 11.65/1.98    introduced(choice_axiom,[])).
% 11.65/1.98  
% 11.65/1.98  fof(f31,plain,(
% 11.65/1.98    (~r1_tarski(k3_subset_1(sK1,sK3),sK2) & r1_tarski(k3_subset_1(sK1,sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.65/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f30,f29])).
% 11.65/1.98  
% 11.65/1.98  fof(f56,plain,(
% 11.65/1.98    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 11.65/1.98    inference(cnf_transformation,[],[f31])).
% 11.65/1.98  
% 11.65/1.98  fof(f16,axiom,(
% 11.65/1.98    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f54,plain,(
% 11.65/1.98    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.65/1.98    inference(cnf_transformation,[],[f16])).
% 11.65/1.98  
% 11.65/1.98  fof(f12,axiom,(
% 11.65/1.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f24,plain,(
% 11.65/1.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.65/1.98    inference(nnf_transformation,[],[f12])).
% 11.65/1.98  
% 11.65/1.98  fof(f25,plain,(
% 11.65/1.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.65/1.98    inference(rectify,[],[f24])).
% 11.65/1.98  
% 11.65/1.98  fof(f26,plain,(
% 11.65/1.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 11.65/1.98    introduced(choice_axiom,[])).
% 11.65/1.98  
% 11.65/1.98  fof(f27,plain,(
% 11.65/1.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.65/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 11.65/1.98  
% 11.65/1.98  fof(f44,plain,(
% 11.65/1.98    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.65/1.98    inference(cnf_transformation,[],[f27])).
% 11.65/1.98  
% 11.65/1.98  fof(f67,plain,(
% 11.65/1.98    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.65/1.98    inference(equality_resolution,[],[f44])).
% 11.65/1.98  
% 11.65/1.98  fof(f2,axiom,(
% 11.65/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f23,plain,(
% 11.65/1.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.65/1.98    inference(nnf_transformation,[],[f2])).
% 11.65/1.98  
% 11.65/1.98  fof(f34,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.65/1.98    inference(cnf_transformation,[],[f23])).
% 11.65/1.98  
% 11.65/1.98  fof(f6,axiom,(
% 11.65/1.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f38,plain,(
% 11.65/1.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.65/1.98    inference(cnf_transformation,[],[f6])).
% 11.65/1.98  
% 11.65/1.98  fof(f15,axiom,(
% 11.65/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f20,plain,(
% 11.65/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.65/1.98    inference(ennf_transformation,[],[f15])).
% 11.65/1.98  
% 11.65/1.98  fof(f53,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.65/1.98    inference(cnf_transformation,[],[f20])).
% 11.65/1.98  
% 11.65/1.98  fof(f55,plain,(
% 11.65/1.98    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.65/1.98    inference(cnf_transformation,[],[f31])).
% 11.65/1.98  
% 11.65/1.98  fof(f57,plain,(
% 11.65/1.98    r1_tarski(k3_subset_1(sK1,sK2),sK3)),
% 11.65/1.98    inference(cnf_transformation,[],[f31])).
% 11.65/1.98  
% 11.65/1.98  fof(f5,axiom,(
% 11.65/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f37,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.65/1.98    inference(cnf_transformation,[],[f5])).
% 11.65/1.98  
% 11.65/1.98  fof(f13,axiom,(
% 11.65/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f48,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.65/1.98    inference(cnf_transformation,[],[f13])).
% 11.65/1.98  
% 11.65/1.98  fof(f11,axiom,(
% 11.65/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f43,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.65/1.98    inference(cnf_transformation,[],[f11])).
% 11.65/1.98  
% 11.65/1.98  fof(f59,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 11.65/1.98    inference(definition_unfolding,[],[f48,f43])).
% 11.65/1.98  
% 11.65/1.98  fof(f62,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 11.65/1.98    inference(definition_unfolding,[],[f37,f59,f59])).
% 11.65/1.98  
% 11.65/1.98  fof(f3,axiom,(
% 11.65/1.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f35,plain,(
% 11.65/1.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.65/1.98    inference(cnf_transformation,[],[f3])).
% 11.65/1.98  
% 11.65/1.98  fof(f61,plain,(
% 11.65/1.98    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 11.65/1.98    inference(definition_unfolding,[],[f35,f59])).
% 11.65/1.98  
% 11.65/1.98  fof(f10,axiom,(
% 11.65/1.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f42,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 11.65/1.98    inference(cnf_transformation,[],[f10])).
% 11.65/1.98  
% 11.65/1.98  fof(f65,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 11.65/1.98    inference(definition_unfolding,[],[f42,f43,f43])).
% 11.65/1.98  
% 11.65/1.98  fof(f7,axiom,(
% 11.65/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f39,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.65/1.98    inference(cnf_transformation,[],[f7])).
% 11.65/1.98  
% 11.65/1.98  fof(f63,plain,(
% 11.65/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1)) )),
% 11.65/1.98    inference(definition_unfolding,[],[f39,f59])).
% 11.65/1.98  
% 11.65/1.98  fof(f4,axiom,(
% 11.65/1.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.65/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.65/1.98  
% 11.65/1.98  fof(f36,plain,(
% 11.65/1.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.65/1.98    inference(cnf_transformation,[],[f4])).
% 11.65/1.98  
% 11.65/1.98  fof(f50,plain,(
% 11.65/1.98    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 11.65/1.98    inference(cnf_transformation,[],[f28])).
% 11.65/1.98  
% 11.65/1.98  fof(f45,plain,(
% 11.65/1.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 11.65/1.98    inference(cnf_transformation,[],[f27])).
% 11.65/1.98  
% 11.65/1.98  fof(f66,plain,(
% 11.65/1.98    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 11.65/1.98    inference(equality_resolution,[],[f45])).
% 11.65/1.98  
% 11.65/1.98  fof(f33,plain,(
% 11.65/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.65/1.98    inference(cnf_transformation,[],[f23])).
% 11.65/1.98  
% 11.65/1.98  fof(f58,plain,(
% 11.65/1.98    ~r1_tarski(k3_subset_1(sK1,sK3),sK2)),
% 11.65/1.98    inference(cnf_transformation,[],[f31])).
% 11.65/1.98  
% 11.65/1.98  cnf(c_0,plain,
% 11.65/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.65/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.65/1.98  
% 11.65/1.98  cnf(c_8,plain,
% 11.65/1.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.65/1.98      inference(cnf_transformation,[],[f64]) ).
% 11.65/1.98  
% 11.65/1.98  cnf(c_2568,plain,
% 11.65/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 11.65/1.98      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 11.65/1.98  
% 11.65/1.98  cnf(c_17,plain,
% 11.65/1.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.65/1.98      inference(cnf_transformation,[],[f49]) ).
% 11.65/1.98  
% 11.65/1.98  cnf(c_22,negated_conjecture,
% 11.65/1.98      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 11.65/1.98      inference(cnf_transformation,[],[f56]) ).
% 11.65/1.98  
% 11.65/1.98  cnf(c_398,plain,
% 11.65/1.99      ( r2_hidden(X0,X1)
% 11.65/1.99      | v1_xboole_0(X1)
% 11.65/1.99      | k1_zfmisc_1(sK1) != X1
% 11.65/1.99      | sK3 != X0 ),
% 11.65/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_399,plain,
% 11.65/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.65/1.99      inference(unflattening,[status(thm)],[c_398]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_19,plain,
% 11.65/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.65/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_405,plain,
% 11.65/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 11.65/1.99      inference(forward_subsumption_resolution,
% 11.65/1.99                [status(thm)],
% 11.65/1.99                [c_399,c_19]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1584,plain,
% 11.65/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.65/1.99      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_13,plain,
% 11.65/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.65/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1587,plain,
% 11.65/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.65/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.65/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2379,plain,
% 11.65/1.99      ( r1_tarski(sK3,sK1) = iProver_top ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_1584,c_1587]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1,plain,
% 11.65/1.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.65/1.99      inference(cnf_transformation,[],[f34]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1593,plain,
% 11.65/1.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 11.65/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.65/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_3778,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,sK1) = k1_xboole_0 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_2379,c_1593]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4148,plain,
% 11.65/1.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,k1_xboole_0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_3778,c_0]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_6,plain,
% 11.65/1.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.65/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4149,plain,
% 11.65/1.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = sK3 ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_4148,c_6]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4144,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),X0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_3778,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4151,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK3,X0) ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_4144,c_6]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5851,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_4149,c_4151]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_18,plain,
% 11.65/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.65/1.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.65/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_23,negated_conjecture,
% 11.65/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 11.65/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_433,plain,
% 11.65/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.65/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.65/1.99      | sK2 != X1 ),
% 11.65/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_434,plain,
% 11.65/1.99      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 11.65/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.65/1.99      inference(unflattening,[status(thm)],[c_433]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1738,plain,
% 11.65/1.99      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 11.65/1.99      inference(equality_resolution,[status(thm)],[c_434]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_21,negated_conjecture,
% 11.65/1.99      ( r1_tarski(k3_subset_1(sK1,sK2),sK3) ),
% 11.65/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1585,plain,
% 11.65/1.99      ( r1_tarski(k3_subset_1(sK1,sK2),sK3) = iProver_top ),
% 11.65/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1802,plain,
% 11.65/1.99      ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_1738,c_1585]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_3780,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),sK3) = k1_xboole_0 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_1802,c_1593]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5,plain,
% 11.65/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
% 11.65/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4043,plain,
% 11.65/1.99      ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k4_xboole_0(sK1,sK2))) = k3_tarski(k2_enumset1(sK3,sK3,sK3,k1_xboole_0)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_3780,c_5]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_3,plain,
% 11.65/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
% 11.65/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4046,plain,
% 11.65/1.99      ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k4_xboole_0(sK1,sK2))) = sK3 ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_4043,c_3]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_9,plain,
% 11.65/1.99      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 11.65/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_7,plain,
% 11.65/1.99      ( k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1) = k4_xboole_0(X0,X1) ),
% 11.65/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2442,plain,
% 11.65/1.99      ( k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X0) = k4_xboole_0(X1,X0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_9,c_7]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4401,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),sK3) = k4_xboole_0(sK3,sK3) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_4046,c_2442]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4402,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_4401,c_3780]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5871,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,k1_xboole_0) ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_5851,c_4402]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5872,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK1,sK3)) = sK3 ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_5871,c_6]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5973,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,sK3),X0))) = k4_xboole_0(k4_xboole_0(sK3,sK3),X0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_5872,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2066,plain,
% 11.65/1.99      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_9,c_3]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2441,plain,
% 11.65/1.99      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_2066,c_7]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2617,plain,
% 11.65/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,X0))) = k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_2441,c_5]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2622,plain,
% 11.65/1.99      ( k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X0,X0))) = X0 ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_2617,c_3]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_3903,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(X0,X0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_2622,c_2442]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4,plain,
% 11.65/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.65/1.99      inference(cnf_transformation,[],[f36]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1591,plain,
% 11.65/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.65/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2251,plain,
% 11.65/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_6,c_1591]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_3782,plain,
% 11.65/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_2251,c_1593]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_3918,plain,
% 11.65/1.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_3903,c_3782]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5978,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,sK3),X0))) = k1_xboole_0 ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_5973,c_3918,c_4402]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4407,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(k4_xboole_0(sK3,k1_xboole_0),X0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_4402,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4426,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK3,X0) ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_4407,c_6]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_7402,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(sK3,k1_xboole_0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_5978,c_4426]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_7709,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) = sK3 ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_7402,c_6]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4040,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X0))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),X0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_3780,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4047,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_4040,c_6]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_8142,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_7709,c_4047]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_8144,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_8142,c_3780]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_8145,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK3),X0)) = k4_xboole_0(sK1,sK2) ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_8144,c_6]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5261,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK3,X0),X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X0),X1) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_4047,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_8127,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK3)))) = sK3 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_0,c_7709]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2249,plain,
% 11.65/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_0,c_1591]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2907,plain,
% 11.65/1.99      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X2) = iProver_top ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_8,c_2249]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2916,plain,
% 11.65/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),X2) = iProver_top ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_2907,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_13605,plain,
% 11.65/1.99      ( r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(sK3,sK3)))),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = iProver_top ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_8127,c_2916]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_7401,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_4151,c_4426]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_13766,plain,
% 11.65/1.99      ( r1_tarski(k4_xboole_0(sK3,k4_xboole_0(sK1,X0)),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = iProver_top ),
% 11.65/1.99      inference(light_normalisation,
% 11.65/1.99                [status(thm)],
% 11.65/1.99                [c_13605,c_6,c_4402,c_7401]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_14394,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK1,X0)),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_13766,c_1593]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_14835,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0)),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_14394,c_5261]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5863,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,k4_xboole_0(sK1,X0))) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_4151,c_4047]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5865,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_5863,c_4047]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_7992,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_5865,c_4047]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_9145,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0)),X1) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_7992,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_9171,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0)),X1) ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_9145,c_7992]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_7399,plain,
% 11.65/1.99      ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = k4_xboole_0(sK3,X0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_0,c_4426]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_9848,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,sK3))) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_7399,c_4047]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_9856,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_9848,c_4047]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_10216,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK3) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_4149,c_9856]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_10290,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k1_xboole_0 ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_10216,c_3780]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_14836,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0)),k4_xboole_0(X0,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 11.65/1.99      inference(demodulation,
% 11.65/1.99                [status(thm)],
% 11.65/1.99                [c_14835,c_6,c_7992,c_9171,c_10290]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_14938,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK1,sK3))))) = k1_xboole_0 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_8,c_14836]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_17791,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,X0))))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X0),k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_5261,c_14938]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_9153,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,X0))) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_7992,c_7992]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_9165,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_9153,c_7992]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4147,plain,
% 11.65/1.99      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_xboole_0)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_3778,c_5]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4150,plain,
% 11.65/1.99      ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)) = sK1 ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_4147,c_3]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4768,plain,
% 11.65/1.99      ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK3,sK1) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_4150,c_2442]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4769,plain,
% 11.65/1.99      ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_4768,c_3778]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5413,plain,
% 11.65/1.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_4769,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5432,plain,
% 11.65/1.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK1,X0) ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_5413,c_6]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_8524,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,k4_xboole_0(sK1,X0))) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_5432,c_5865]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_8530,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_8524,c_5865]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_9166,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_9165,c_8530]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_17984,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),X0),k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 11.65/1.99      inference(light_normalisation,
% 11.65/1.99                [status(thm)],
% 11.65/1.99                [c_17791,c_4047,c_9166]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_19394,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_0,c_17984]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2580,plain,
% 11.65/1.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_8,c_1591]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_16,plain,
% 11.65/1.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.65/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_377,plain,
% 11.65/1.99      ( ~ r2_hidden(X0,X1)
% 11.65/1.99      | v1_xboole_0(X1)
% 11.65/1.99      | X2 != X0
% 11.65/1.99      | k3_subset_1(X3,X2) = k4_xboole_0(X3,X2)
% 11.65/1.99      | k1_zfmisc_1(X3) != X1 ),
% 11.65/1.99      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_378,plain,
% 11.65/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 11.65/1.99      | v1_xboole_0(k1_zfmisc_1(X1))
% 11.65/1.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.65/1.99      inference(unflattening,[status(thm)],[c_377]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_12,plain,
% 11.65/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.65/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_149,plain,
% 11.65/1.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.65/1.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_150,plain,
% 11.65/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.65/1.99      inference(renaming,[status(thm)],[c_149]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_321,plain,
% 11.65/1.99      ( m1_subset_1(X0,X1)
% 11.65/1.99      | ~ r1_tarski(X2,X3)
% 11.65/1.99      | v1_xboole_0(X1)
% 11.65/1.99      | X0 != X2
% 11.65/1.99      | k1_zfmisc_1(X3) != X1 ),
% 11.65/1.99      inference(resolution_lifted,[status(thm)],[c_150,c_16]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_322,plain,
% 11.65/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.65/1.99      | ~ r1_tarski(X0,X1)
% 11.65/1.99      | v1_xboole_0(k1_zfmisc_1(X1)) ),
% 11.65/1.99      inference(unflattening,[status(thm)],[c_321]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_332,plain,
% 11.65/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.65/1.99      inference(forward_subsumption_resolution,
% 11.65/1.99                [status(thm)],
% 11.65/1.99                [c_322,c_19]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_382,plain,
% 11.65/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
% 11.65/1.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.65/1.99      inference(global_propositional_subsumption,
% 11.65/1.99                [status(thm)],
% 11.65/1.99                [c_378,c_18,c_13,c_332]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_845,plain,
% 11.65/1.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.65/1.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_846,plain,
% 11.65/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.65/1.99      inference(renaming,[status(thm)],[c_845]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_878,plain,
% 11.65/1.99      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.65/1.99      inference(bin_hyper_res,[status(thm)],[c_382,c_846]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1582,plain,
% 11.65/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.65/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.65/1.99      inference(predicate_to_equality,[status(thm)],[c_878]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_6575,plain,
% 11.65/1.99      ( k3_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_2580,c_1582]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2252,plain,
% 11.65/1.99      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_1591,c_1582]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5519,plain,
% 11.65/1.99      ( k3_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_8,c_2252]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5571,plain,
% 11.65/1.99      ( k3_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_5519,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5572,plain,
% 11.65/1.99      ( k3_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_5571,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_6576,plain,
% 11.65/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_6575,c_5572]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_19507,plain,
% 11.65/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3))))))) = k1_xboole_0 ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_19394,c_8,c_6576]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5975,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3)) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_5872,c_4047]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5976,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3)) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_5975,c_3780]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_5977,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK1,sK2) ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_5976,c_6]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_9124,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_0,c_7992]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_9193,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,sK2),X0) ),
% 11.65/1.99      inference(demodulation,[status(thm)],[c_9124,c_9166]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_19508,plain,
% 11.65/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) = k1_xboole_0 ),
% 11.65/1.99      inference(light_normalisation,
% 11.65/1.99                [status(thm)],
% 11.65/1.99                [c_19507,c_5977,c_9193]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_19597,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK3),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK3),X0),k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_8145,c_19508]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_34366,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK3),X0))),sK2) = k1_xboole_0 ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_2568,c_19597]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_4628,plain,
% 11.65/1.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK3),X0))) = k4_xboole_0(k4_xboole_0(sK1,sK3),X0) ),
% 11.65/1.99      inference(superposition,[status(thm)],[c_4149,c_8]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_34860,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK3),X0),sK2) = k1_xboole_0 ),
% 11.65/1.99      inference(light_normalisation,[status(thm)],[c_34366,c_4628]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_35385,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0),sK2) = k1_xboole_0 ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_34860]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2,plain,
% 11.65/1.99      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.65/1.99      inference(cnf_transformation,[],[f33]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1838,plain,
% 11.65/1.99      ( r1_tarski(X0,sK2) | k4_xboole_0(X0,sK2) != k1_xboole_0 ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_11309,plain,
% 11.65/1.99      ( r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0),sK2)
% 11.65/1.99      | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0),sK2) != k1_xboole_0 ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_1838]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1265,plain,
% 11.65/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.65/1.99      theory(equality) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1616,plain,
% 11.65/1.99      ( ~ r1_tarski(X0,X1)
% 11.65/1.99      | r1_tarski(k3_subset_1(sK1,sK3),sK2)
% 11.65/1.99      | k3_subset_1(sK1,sK3) != X0
% 11.65/1.99      | sK2 != X1 ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_1265]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1654,plain,
% 11.65/1.99      ( ~ r1_tarski(X0,sK2)
% 11.65/1.99      | r1_tarski(k3_subset_1(sK1,sK3),sK2)
% 11.65/1.99      | k3_subset_1(sK1,sK3) != X0
% 11.65/1.99      | sK2 != sK2 ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_1616]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_7857,plain,
% 11.65/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),sK2)
% 11.65/1.99      | ~ r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0),sK2)
% 11.65/1.99      | k3_subset_1(sK1,sK3) != k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)
% 11.65/1.99      | sK2 != sK2 ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_1654]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_3146,plain,
% 11.65/1.99      ( k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k4_xboole_0(sK1,sK3) ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1263,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1943,plain,
% 11.65/1.99      ( X0 != X1
% 11.65/1.99      | k3_subset_1(sK1,sK3) != X1
% 11.65/1.99      | k3_subset_1(sK1,sK3) = X0 ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_1263]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2163,plain,
% 11.65/1.99      ( X0 != k4_xboole_0(sK1,sK3)
% 11.65/1.99      | k3_subset_1(sK1,sK3) = X0
% 11.65/1.99      | k3_subset_1(sK1,sK3) != k4_xboole_0(sK1,sK3) ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_1943]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_2189,plain,
% 11.65/1.99      ( k3_subset_1(sK1,sK3) = k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)
% 11.65/1.99      | k3_subset_1(sK1,sK3) != k4_xboole_0(sK1,sK3)
% 11.65/1.99      | k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) != k4_xboole_0(sK1,sK3) ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_2163]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1262,plain,( X0 = X0 ),theory(equality) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1709,plain,
% 11.65/1.99      ( sK2 = sK2 ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_1262]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1662,plain,
% 11.65/1.99      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_1262]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_424,plain,
% 11.65/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.65/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.65/1.99      | sK3 != X1 ),
% 11.65/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_425,plain,
% 11.65/1.99      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 11.65/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.65/1.99      inference(unflattening,[status(thm)],[c_424]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_1631,plain,
% 11.65/1.99      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3)
% 11.65/1.99      | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 11.65/1.99      inference(instantiation,[status(thm)],[c_425]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(c_20,negated_conjecture,
% 11.65/1.99      ( ~ r1_tarski(k3_subset_1(sK1,sK3),sK2) ),
% 11.65/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.65/1.99  
% 11.65/1.99  cnf(contradiction,plain,
% 11.65/1.99      ( $false ),
% 11.65/1.99      inference(minisat,
% 11.65/1.99                [status(thm)],
% 11.65/1.99                [c_35385,c_11309,c_7857,c_3146,c_2189,c_1709,c_1662,
% 11.65/1.99                 c_1631,c_20]) ).
% 11.65/1.99  
% 11.65/1.99  
% 11.65/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.65/1.99  
% 11.65/1.99  ------                               Statistics
% 11.65/1.99  
% 11.65/1.99  ------ General
% 11.65/1.99  
% 11.65/1.99  abstr_ref_over_cycles:                  0
% 11.65/1.99  abstr_ref_under_cycles:                 0
% 11.65/1.99  gc_basic_clause_elim:                   0
% 11.65/1.99  forced_gc_time:                         0
% 11.65/1.99  parsing_time:                           0.008
% 11.65/1.99  unif_index_cands_time:                  0.
% 11.65/1.99  unif_index_add_time:                    0.
% 11.65/1.99  orderings_time:                         0.
% 11.65/1.99  out_proof_time:                         0.011
% 11.65/1.99  total_time:                             1.016
% 11.65/1.99  num_of_symbols:                         45
% 11.65/1.99  num_of_terms:                           49048
% 11.65/1.99  
% 11.65/1.99  ------ Preprocessing
% 11.65/1.99  
% 11.65/1.99  num_of_splits:                          0
% 11.65/1.99  num_of_split_atoms:                     0
% 11.65/1.99  num_of_reused_defs:                     0
% 11.65/1.99  num_eq_ax_congr_red:                    15
% 11.65/1.99  num_of_sem_filtered_clauses:            1
% 11.65/1.99  num_of_subtypes:                        0
% 11.65/1.99  monotx_restored_types:                  0
% 11.65/1.99  sat_num_of_epr_types:                   0
% 11.65/1.99  sat_num_of_non_cyclic_types:            0
% 11.65/1.99  sat_guarded_non_collapsed_types:        0
% 11.65/1.99  num_pure_diseq_elim:                    0
% 11.65/1.99  simp_replaced_by:                       0
% 11.65/1.99  res_preprocessed:                       106
% 11.65/1.99  prep_upred:                             0
% 11.65/1.99  prep_unflattend:                        100
% 11.65/1.99  smt_new_axioms:                         0
% 11.65/1.99  pred_elim_cands:                        2
% 11.65/1.99  pred_elim:                              2
% 11.65/1.99  pred_elim_cl:                           3
% 11.65/1.99  pred_elim_cycles:                       7
% 11.65/1.99  merged_defs:                            16
% 11.65/1.99  merged_defs_ncl:                        0
% 11.65/1.99  bin_hyper_res:                          17
% 11.65/1.99  prep_cycles:                            4
% 11.65/1.99  pred_elim_time:                         0.013
% 11.65/1.99  splitting_time:                         0.
% 11.65/1.99  sem_filter_time:                        0.
% 11.65/1.99  monotx_time:                            0.
% 11.65/1.99  subtype_inf_time:                       0.
% 11.65/1.99  
% 11.65/1.99  ------ Problem properties
% 11.65/1.99  
% 11.65/1.99  clauses:                                21
% 11.65/1.99  conjectures:                            2
% 11.65/1.99  epr:                                    0
% 11.65/1.99  horn:                                   20
% 11.65/1.99  ground:                                 4
% 11.65/1.99  unary:                                  12
% 11.65/1.99  binary:                                 7
% 11.65/1.99  lits:                                   32
% 11.65/1.99  lits_eq:                                16
% 11.65/1.99  fd_pure:                                0
% 11.65/1.99  fd_pseudo:                              0
% 11.65/1.99  fd_cond:                                0
% 11.65/1.99  fd_pseudo_cond:                         2
% 11.65/1.99  ac_symbols:                             0
% 11.65/1.99  
% 11.65/1.99  ------ Propositional Solver
% 11.65/1.99  
% 11.65/1.99  prop_solver_calls:                      33
% 11.65/1.99  prop_fast_solver_calls:                 858
% 11.65/1.99  smt_solver_calls:                       0
% 11.65/1.99  smt_fast_solver_calls:                  0
% 11.65/1.99  prop_num_of_clauses:                    11142
% 11.65/1.99  prop_preprocess_simplified:             14527
% 11.65/1.99  prop_fo_subsumed:                       6
% 11.65/1.99  prop_solver_time:                       0.
% 11.65/1.99  smt_solver_time:                        0.
% 11.65/1.99  smt_fast_solver_time:                   0.
% 11.65/1.99  prop_fast_solver_time:                  0.
% 11.65/1.99  prop_unsat_core_time:                   0.001
% 11.65/1.99  
% 11.65/1.99  ------ QBF
% 11.65/1.99  
% 11.65/1.99  qbf_q_res:                              0
% 11.65/1.99  qbf_num_tautologies:                    0
% 11.65/1.99  qbf_prep_cycles:                        0
% 11.65/1.99  
% 11.65/1.99  ------ BMC1
% 11.65/1.99  
% 11.65/1.99  bmc1_current_bound:                     -1
% 11.65/1.99  bmc1_last_solved_bound:                 -1
% 11.65/1.99  bmc1_unsat_core_size:                   -1
% 11.65/1.99  bmc1_unsat_core_parents_size:           -1
% 11.65/1.99  bmc1_merge_next_fun:                    0
% 11.65/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.65/1.99  
% 11.65/1.99  ------ Instantiation
% 11.65/1.99  
% 11.65/1.99  inst_num_of_clauses:                    2398
% 11.65/1.99  inst_num_in_passive:                    1166
% 11.65/1.99  inst_num_in_active:                     1069
% 11.65/1.99  inst_num_in_unprocessed:                163
% 11.65/1.99  inst_num_of_loops:                      1300
% 11.65/1.99  inst_num_of_learning_restarts:          0
% 11.65/1.99  inst_num_moves_active_passive:          227
% 11.65/1.99  inst_lit_activity:                      0
% 11.65/1.99  inst_lit_activity_moves:                0
% 11.65/1.99  inst_num_tautologies:                   0
% 11.65/1.99  inst_num_prop_implied:                  0
% 11.65/1.99  inst_num_existing_simplified:           0
% 11.65/1.99  inst_num_eq_res_simplified:             0
% 11.65/1.99  inst_num_child_elim:                    0
% 11.65/1.99  inst_num_of_dismatching_blockings:      2150
% 11.65/1.99  inst_num_of_non_proper_insts:           3445
% 11.65/1.99  inst_num_of_duplicates:                 0
% 11.65/1.99  inst_inst_num_from_inst_to_res:         0
% 11.65/1.99  inst_dismatching_checking_time:         0.
% 11.65/1.99  
% 11.65/1.99  ------ Resolution
% 11.65/1.99  
% 11.65/1.99  res_num_of_clauses:                     0
% 11.65/1.99  res_num_in_passive:                     0
% 11.65/1.99  res_num_in_active:                      0
% 11.65/1.99  res_num_of_loops:                       110
% 11.65/1.99  res_forward_subset_subsumed:            466
% 11.65/1.99  res_backward_subset_subsumed:           0
% 11.65/1.99  res_forward_subsumed:                   3
% 11.65/1.99  res_backward_subsumed:                  0
% 11.65/1.99  res_forward_subsumption_resolution:     4
% 11.65/1.99  res_backward_subsumption_resolution:    0
% 11.65/1.99  res_clause_to_clause_subsumption:       19584
% 11.65/1.99  res_orphan_elimination:                 0
% 11.65/1.99  res_tautology_del:                      396
% 11.65/1.99  res_num_eq_res_simplified:              0
% 11.65/1.99  res_num_sel_changes:                    0
% 11.65/1.99  res_moves_from_active_to_pass:          0
% 11.65/1.99  
% 11.65/1.99  ------ Superposition
% 11.65/1.99  
% 11.65/1.99  sup_time_total:                         0.
% 11.65/1.99  sup_time_generating:                    0.
% 11.65/1.99  sup_time_sim_full:                      0.
% 11.65/1.99  sup_time_sim_immed:                     0.
% 11.65/1.99  
% 11.65/1.99  sup_num_of_clauses:                     1772
% 11.65/1.99  sup_num_in_active:                      236
% 11.65/1.99  sup_num_in_passive:                     1536
% 11.65/1.99  sup_num_of_loops:                       259
% 11.65/1.99  sup_fw_superposition:                   4449
% 11.65/1.99  sup_bw_superposition:                   2637
% 11.65/1.99  sup_immediate_simplified:               5227
% 11.65/1.99  sup_given_eliminated:                   8
% 11.65/1.99  comparisons_done:                       0
% 11.65/1.99  comparisons_avoided:                    0
% 11.65/1.99  
% 11.65/1.99  ------ Simplifications
% 11.65/1.99  
% 11.65/1.99  
% 11.65/1.99  sim_fw_subset_subsumed:                 42
% 11.65/1.99  sim_bw_subset_subsumed:                 0
% 11.65/1.99  sim_fw_subsumed:                        615
% 11.65/1.99  sim_bw_subsumed:                        52
% 11.65/1.99  sim_fw_subsumption_res:                 0
% 11.65/1.99  sim_bw_subsumption_res:                 0
% 11.65/1.99  sim_tautology_del:                      2
% 11.65/1.99  sim_eq_tautology_del:                   808
% 11.65/1.99  sim_eq_res_simp:                        102
% 11.65/1.99  sim_fw_demodulated:                     4260
% 11.65/1.99  sim_bw_demodulated:                     131
% 11.65/1.99  sim_light_normalised:                   2887
% 11.65/1.99  sim_joinable_taut:                      0
% 11.65/1.99  sim_joinable_simp:                      0
% 11.65/1.99  sim_ac_normalised:                      0
% 11.65/1.99  sim_smt_subsumption:                    0
% 11.65/1.99  
%------------------------------------------------------------------------------
