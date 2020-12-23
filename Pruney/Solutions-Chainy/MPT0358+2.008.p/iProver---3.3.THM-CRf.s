%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:49 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 322 expanded)
%              Number of clauses        :   70 ( 116 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  330 ( 972 expanded)
%              Number of equality atoms :  141 ( 338 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f40])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK1) != sK2
        | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & ( k1_subset_1(sK1) = sK2
        | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( k1_subset_1(sK1) != sK2
      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & ( k1_subset_1(sK1) = sK2
      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f34])).

fof(f60,plain,
    ( k1_subset_1(sK1) = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f60,f54])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f61,plain,
    ( k1_subset_1(sK1) != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,
    ( k1_xboole_0 != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f61,f54])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_926,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_919,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_915,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2285,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_919,c_915])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_911,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2285,c_911])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_913,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4649,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4642,c_913])).

cnf(c_5658,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_926,c_4649])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_923,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5660,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_923,c_4649])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5689,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5660,c_7])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_910,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4650,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4642,c_910])).

cnf(c_4865,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_923,c_4650])).

cnf(c_5917,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5689,c_4865])).

cnf(c_6186,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5658,c_5917])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_922,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2972,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_922])).

cnf(c_6195,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6186,c_2972])).

cnf(c_6215,plain,
    ( r1_xboole_0(sK2,sK2) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6195])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_908,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_907,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2155,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_907,c_913])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_925,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3866,plain,
    ( r1_xboole_0(X0,sK2) = iProver_top
    | r1_tarski(X0,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_925])).

cnf(c_4681,plain,
    ( sK2 = k1_xboole_0
    | r1_xboole_0(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_908,c_3866])).

cnf(c_416,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1226,plain,
    ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_419,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1172,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,sK2) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_1225,plain,
    ( ~ r1_tarski(X0,k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_1366,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_1368,plain,
    ( k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
    | sK2 != k1_xboole_0
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1366])).

cnf(c_1367,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1370,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1367])).

cnf(c_3894,plain,
    ( r1_xboole_0(sK2,sK2) = iProver_top
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3866])).

cnf(c_4855,plain,
    ( r1_xboole_0(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4681,c_1226,c_1368,c_1370,c_3894])).

cnf(c_3865,plain,
    ( r1_xboole_0(X0,sK2) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_922])).

cnf(c_3891,plain,
    ( r1_xboole_0(sK2,sK2) != iProver_top
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3865])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_927,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2417,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_927])).

cnf(c_2430,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1390,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[status(thm)],[c_16,c_23])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1352,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1536,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1390,c_23,c_1109,c_1352])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1736,plain,
    ( r1_tarski(sK2,sK1) ),
    inference(resolution,[status(thm)],[c_1536,c_12])).

cnf(c_1737,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1736])).

cnf(c_74,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_76,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,plain,
    ( k1_xboole_0 != sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6215,c_4855,c_3891,c_2430,c_1737,c_76,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:18:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.48/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/0.99  
% 3.48/0.99  ------  iProver source info
% 3.48/0.99  
% 3.48/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.48/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/0.99  git: non_committed_changes: false
% 3.48/0.99  git: last_make_outside_of_git: false
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options
% 3.48/0.99  
% 3.48/0.99  --out_options                           all
% 3.48/0.99  --tptp_safe_out                         true
% 3.48/0.99  --problem_path                          ""
% 3.48/0.99  --include_path                          ""
% 3.48/0.99  --clausifier                            res/vclausify_rel
% 3.48/0.99  --clausifier_options                    --mode clausify
% 3.48/0.99  --stdin                                 false
% 3.48/0.99  --stats_out                             sel
% 3.48/0.99  
% 3.48/0.99  ------ General Options
% 3.48/0.99  
% 3.48/0.99  --fof                                   false
% 3.48/0.99  --time_out_real                         604.99
% 3.48/0.99  --time_out_virtual                      -1.
% 3.48/0.99  --symbol_type_check                     false
% 3.48/0.99  --clausify_out                          false
% 3.48/0.99  --sig_cnt_out                           false
% 3.48/0.99  --trig_cnt_out                          false
% 3.48/0.99  --trig_cnt_out_tolerance                1.
% 3.48/0.99  --trig_cnt_out_sk_spl                   false
% 3.48/0.99  --abstr_cl_out                          false
% 3.48/0.99  
% 3.48/0.99  ------ Global Options
% 3.48/0.99  
% 3.48/0.99  --schedule                              none
% 3.48/0.99  --add_important_lit                     false
% 3.48/0.99  --prop_solver_per_cl                    1000
% 3.48/0.99  --min_unsat_core                        false
% 3.48/0.99  --soft_assumptions                      false
% 3.48/0.99  --soft_lemma_size                       3
% 3.48/0.99  --prop_impl_unit_size                   0
% 3.48/0.99  --prop_impl_unit                        []
% 3.48/0.99  --share_sel_clauses                     true
% 3.48/0.99  --reset_solvers                         false
% 3.48/0.99  --bc_imp_inh                            [conj_cone]
% 3.48/0.99  --conj_cone_tolerance                   3.
% 3.48/0.99  --extra_neg_conj                        none
% 3.48/0.99  --large_theory_mode                     true
% 3.48/0.99  --prolific_symb_bound                   200
% 3.48/0.99  --lt_threshold                          2000
% 3.48/0.99  --clause_weak_htbl                      true
% 3.48/0.99  --gc_record_bc_elim                     false
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing Options
% 3.48/0.99  
% 3.48/0.99  --preprocessing_flag                    true
% 3.48/0.99  --time_out_prep_mult                    0.1
% 3.48/0.99  --splitting_mode                        input
% 3.48/0.99  --splitting_grd                         true
% 3.48/0.99  --splitting_cvd                         false
% 3.48/0.99  --splitting_cvd_svl                     false
% 3.48/0.99  --splitting_nvd                         32
% 3.48/0.99  --sub_typing                            true
% 3.48/0.99  --prep_gs_sim                           false
% 3.48/0.99  --prep_unflatten                        true
% 3.48/0.99  --prep_res_sim                          true
% 3.48/0.99  --prep_upred                            true
% 3.48/0.99  --prep_sem_filter                       exhaustive
% 3.48/0.99  --prep_sem_filter_out                   false
% 3.48/0.99  --pred_elim                             false
% 3.48/0.99  --res_sim_input                         true
% 3.48/0.99  --eq_ax_congr_red                       true
% 3.48/0.99  --pure_diseq_elim                       true
% 3.48/0.99  --brand_transform                       false
% 3.48/0.99  --non_eq_to_eq                          false
% 3.48/0.99  --prep_def_merge                        true
% 3.48/0.99  --prep_def_merge_prop_impl              false
% 3.48/0.99  --prep_def_merge_mbd                    true
% 3.48/0.99  --prep_def_merge_tr_red                 false
% 3.48/0.99  --prep_def_merge_tr_cl                  false
% 3.48/0.99  --smt_preprocessing                     true
% 3.48/0.99  --smt_ac_axioms                         fast
% 3.48/0.99  --preprocessed_out                      false
% 3.48/0.99  --preprocessed_stats                    false
% 3.48/0.99  
% 3.48/0.99  ------ Abstraction refinement Options
% 3.48/0.99  
% 3.48/0.99  --abstr_ref                             []
% 3.48/0.99  --abstr_ref_prep                        false
% 3.48/0.99  --abstr_ref_until_sat                   false
% 3.48/0.99  --abstr_ref_sig_restrict                funpre
% 3.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/0.99  --abstr_ref_under                       []
% 3.48/0.99  
% 3.48/0.99  ------ SAT Options
% 3.48/0.99  
% 3.48/0.99  --sat_mode                              false
% 3.48/0.99  --sat_fm_restart_options                ""
% 3.48/0.99  --sat_gr_def                            false
% 3.48/0.99  --sat_epr_types                         true
% 3.48/0.99  --sat_non_cyclic_types                  false
% 3.48/0.99  --sat_finite_models                     false
% 3.48/0.99  --sat_fm_lemmas                         false
% 3.48/0.99  --sat_fm_prep                           false
% 3.48/0.99  --sat_fm_uc_incr                        true
% 3.48/0.99  --sat_out_model                         small
% 3.48/0.99  --sat_out_clauses                       false
% 3.48/0.99  
% 3.48/0.99  ------ QBF Options
% 3.48/0.99  
% 3.48/0.99  --qbf_mode                              false
% 3.48/0.99  --qbf_elim_univ                         false
% 3.48/0.99  --qbf_dom_inst                          none
% 3.48/0.99  --qbf_dom_pre_inst                      false
% 3.48/0.99  --qbf_sk_in                             false
% 3.48/0.99  --qbf_pred_elim                         true
% 3.48/0.99  --qbf_split                             512
% 3.48/0.99  
% 3.48/0.99  ------ BMC1 Options
% 3.48/0.99  
% 3.48/0.99  --bmc1_incremental                      false
% 3.48/0.99  --bmc1_axioms                           reachable_all
% 3.48/0.99  --bmc1_min_bound                        0
% 3.48/0.99  --bmc1_max_bound                        -1
% 3.48/0.99  --bmc1_max_bound_default                -1
% 3.48/0.99  --bmc1_symbol_reachability              true
% 3.48/0.99  --bmc1_property_lemmas                  false
% 3.48/0.99  --bmc1_k_induction                      false
% 3.48/0.99  --bmc1_non_equiv_states                 false
% 3.48/0.99  --bmc1_deadlock                         false
% 3.48/0.99  --bmc1_ucm                              false
% 3.48/0.99  --bmc1_add_unsat_core                   none
% 3.48/0.99  --bmc1_unsat_core_children              false
% 3.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/0.99  --bmc1_out_stat                         full
% 3.48/0.99  --bmc1_ground_init                      false
% 3.48/0.99  --bmc1_pre_inst_next_state              false
% 3.48/0.99  --bmc1_pre_inst_state                   false
% 3.48/0.99  --bmc1_pre_inst_reach_state             false
% 3.48/0.99  --bmc1_out_unsat_core                   false
% 3.48/0.99  --bmc1_aig_witness_out                  false
% 3.48/0.99  --bmc1_verbose                          false
% 3.48/0.99  --bmc1_dump_clauses_tptp                false
% 3.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.48/0.99  --bmc1_dump_file                        -
% 3.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.48/0.99  --bmc1_ucm_extend_mode                  1
% 3.48/0.99  --bmc1_ucm_init_mode                    2
% 3.48/0.99  --bmc1_ucm_cone_mode                    none
% 3.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.48/0.99  --bmc1_ucm_relax_model                  4
% 3.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/0.99  --bmc1_ucm_layered_model                none
% 3.48/0.99  --bmc1_ucm_max_lemma_size               10
% 3.48/0.99  
% 3.48/0.99  ------ AIG Options
% 3.48/0.99  
% 3.48/0.99  --aig_mode                              false
% 3.48/0.99  
% 3.48/0.99  ------ Instantiation Options
% 3.48/0.99  
% 3.48/0.99  --instantiation_flag                    true
% 3.48/0.99  --inst_sos_flag                         false
% 3.48/0.99  --inst_sos_phase                        true
% 3.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel_side                     num_symb
% 3.48/0.99  --inst_solver_per_active                1400
% 3.48/0.99  --inst_solver_calls_frac                1.
% 3.48/0.99  --inst_passive_queue_type               priority_queues
% 3.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/0.99  --inst_passive_queues_freq              [25;2]
% 3.48/0.99  --inst_dismatching                      true
% 3.48/0.99  --inst_eager_unprocessed_to_passive     true
% 3.48/0.99  --inst_prop_sim_given                   true
% 3.48/0.99  --inst_prop_sim_new                     false
% 3.48/0.99  --inst_subs_new                         false
% 3.48/0.99  --inst_eq_res_simp                      false
% 3.48/0.99  --inst_subs_given                       false
% 3.48/0.99  --inst_orphan_elimination               true
% 3.48/0.99  --inst_learning_loop_flag               true
% 3.48/0.99  --inst_learning_start                   3000
% 3.48/0.99  --inst_learning_factor                  2
% 3.48/0.99  --inst_start_prop_sim_after_learn       3
% 3.48/0.99  --inst_sel_renew                        solver
% 3.48/0.99  --inst_lit_activity_flag                true
% 3.48/0.99  --inst_restr_to_given                   false
% 3.48/0.99  --inst_activity_threshold               500
% 3.48/0.99  --inst_out_proof                        true
% 3.48/0.99  
% 3.48/0.99  ------ Resolution Options
% 3.48/0.99  
% 3.48/0.99  --resolution_flag                       true
% 3.48/0.99  --res_lit_sel                           adaptive
% 3.48/0.99  --res_lit_sel_side                      none
% 3.48/0.99  --res_ordering                          kbo
% 3.48/0.99  --res_to_prop_solver                    active
% 3.48/0.99  --res_prop_simpl_new                    false
% 3.48/0.99  --res_prop_simpl_given                  true
% 3.48/0.99  --res_passive_queue_type                priority_queues
% 3.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/0.99  --res_passive_queues_freq               [15;5]
% 3.48/0.99  --res_forward_subs                      full
% 3.48/0.99  --res_backward_subs                     full
% 3.48/0.99  --res_forward_subs_resolution           true
% 3.48/0.99  --res_backward_subs_resolution          true
% 3.48/0.99  --res_orphan_elimination                true
% 3.48/0.99  --res_time_limit                        2.
% 3.48/0.99  --res_out_proof                         true
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Options
% 3.48/0.99  
% 3.48/0.99  --superposition_flag                    true
% 3.48/0.99  --sup_passive_queue_type                priority_queues
% 3.48/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/0.99  --sup_passive_queues_freq               [1;4]
% 3.48/0.99  --demod_completeness_check              fast
% 3.48/0.99  --demod_use_ground                      true
% 3.48/0.99  --sup_to_prop_solver                    passive
% 3.48/0.99  --sup_prop_simpl_new                    true
% 3.48/0.99  --sup_prop_simpl_given                  true
% 3.48/0.99  --sup_fun_splitting                     false
% 3.48/0.99  --sup_smt_interval                      50000
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Simplification Setup
% 3.48/0.99  
% 3.48/0.99  --sup_indices_passive                   []
% 3.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_full_bw                           [BwDemod]
% 3.48/0.99  --sup_immed_triv                        [TrivRules]
% 3.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_immed_bw_main                     []
% 3.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  
% 3.48/0.99  ------ Combination Options
% 3.48/0.99  
% 3.48/0.99  --comb_res_mult                         3
% 3.48/0.99  --comb_sup_mult                         2
% 3.48/0.99  --comb_inst_mult                        10
% 3.48/0.99  
% 3.48/0.99  ------ Debug Options
% 3.48/0.99  
% 3.48/0.99  --dbg_backtrace                         false
% 3.48/0.99  --dbg_dump_prop_clauses                 false
% 3.48/0.99  --dbg_dump_prop_clauses_file            -
% 3.48/0.99  --dbg_out_stat                          false
% 3.48/0.99  ------ Parsing...
% 3.48/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  ------ Proving...
% 3.48/0.99  ------ Problem Properties 
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  clauses                                 23
% 3.48/0.99  conjectures                             3
% 3.48/0.99  EPR                                     7
% 3.48/0.99  Horn                                    19
% 3.48/0.99  unary                                   6
% 3.48/0.99  binary                                  9
% 3.48/0.99  lits                                    48
% 3.48/0.99  lits eq                                 9
% 3.48/0.99  fd_pure                                 0
% 3.48/0.99  fd_pseudo                               0
% 3.48/0.99  fd_cond                                 0
% 3.48/0.99  fd_pseudo_cond                          3
% 3.48/0.99  AC symbols                              0
% 3.48/0.99  
% 3.48/0.99  ------ Input Options Time Limit: Unbounded
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  Current options:
% 3.48/0.99  ------ 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options
% 3.48/0.99  
% 3.48/0.99  --out_options                           all
% 3.48/0.99  --tptp_safe_out                         true
% 3.48/0.99  --problem_path                          ""
% 3.48/0.99  --include_path                          ""
% 3.48/0.99  --clausifier                            res/vclausify_rel
% 3.48/0.99  --clausifier_options                    --mode clausify
% 3.48/0.99  --stdin                                 false
% 3.48/0.99  --stats_out                             sel
% 3.48/0.99  
% 3.48/0.99  ------ General Options
% 3.48/0.99  
% 3.48/0.99  --fof                                   false
% 3.48/0.99  --time_out_real                         604.99
% 3.48/0.99  --time_out_virtual                      -1.
% 3.48/0.99  --symbol_type_check                     false
% 3.48/0.99  --clausify_out                          false
% 3.48/0.99  --sig_cnt_out                           false
% 3.48/0.99  --trig_cnt_out                          false
% 3.48/0.99  --trig_cnt_out_tolerance                1.
% 3.48/0.99  --trig_cnt_out_sk_spl                   false
% 3.48/0.99  --abstr_cl_out                          false
% 3.48/0.99  
% 3.48/0.99  ------ Global Options
% 3.48/0.99  
% 3.48/0.99  --schedule                              none
% 3.48/0.99  --add_important_lit                     false
% 3.48/0.99  --prop_solver_per_cl                    1000
% 3.48/0.99  --min_unsat_core                        false
% 3.48/0.99  --soft_assumptions                      false
% 3.48/0.99  --soft_lemma_size                       3
% 3.48/0.99  --prop_impl_unit_size                   0
% 3.48/0.99  --prop_impl_unit                        []
% 3.48/0.99  --share_sel_clauses                     true
% 3.48/0.99  --reset_solvers                         false
% 3.48/0.99  --bc_imp_inh                            [conj_cone]
% 3.48/0.99  --conj_cone_tolerance                   3.
% 3.48/0.99  --extra_neg_conj                        none
% 3.48/0.99  --large_theory_mode                     true
% 3.48/0.99  --prolific_symb_bound                   200
% 3.48/0.99  --lt_threshold                          2000
% 3.48/0.99  --clause_weak_htbl                      true
% 3.48/0.99  --gc_record_bc_elim                     false
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing Options
% 3.48/0.99  
% 3.48/0.99  --preprocessing_flag                    true
% 3.48/0.99  --time_out_prep_mult                    0.1
% 3.48/0.99  --splitting_mode                        input
% 3.48/0.99  --splitting_grd                         true
% 3.48/0.99  --splitting_cvd                         false
% 3.48/0.99  --splitting_cvd_svl                     false
% 3.48/0.99  --splitting_nvd                         32
% 3.48/0.99  --sub_typing                            true
% 3.48/0.99  --prep_gs_sim                           false
% 3.48/0.99  --prep_unflatten                        true
% 3.48/0.99  --prep_res_sim                          true
% 3.48/0.99  --prep_upred                            true
% 3.48/0.99  --prep_sem_filter                       exhaustive
% 3.48/0.99  --prep_sem_filter_out                   false
% 3.48/0.99  --pred_elim                             false
% 3.48/0.99  --res_sim_input                         true
% 3.48/0.99  --eq_ax_congr_red                       true
% 3.48/0.99  --pure_diseq_elim                       true
% 3.48/0.99  --brand_transform                       false
% 3.48/0.99  --non_eq_to_eq                          false
% 3.48/0.99  --prep_def_merge                        true
% 3.48/0.99  --prep_def_merge_prop_impl              false
% 3.48/0.99  --prep_def_merge_mbd                    true
% 3.48/0.99  --prep_def_merge_tr_red                 false
% 3.48/0.99  --prep_def_merge_tr_cl                  false
% 3.48/0.99  --smt_preprocessing                     true
% 3.48/0.99  --smt_ac_axioms                         fast
% 3.48/0.99  --preprocessed_out                      false
% 3.48/0.99  --preprocessed_stats                    false
% 3.48/0.99  
% 3.48/0.99  ------ Abstraction refinement Options
% 3.48/0.99  
% 3.48/0.99  --abstr_ref                             []
% 3.48/0.99  --abstr_ref_prep                        false
% 3.48/0.99  --abstr_ref_until_sat                   false
% 3.48/0.99  --abstr_ref_sig_restrict                funpre
% 3.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/0.99  --abstr_ref_under                       []
% 3.48/0.99  
% 3.48/0.99  ------ SAT Options
% 3.48/0.99  
% 3.48/0.99  --sat_mode                              false
% 3.48/0.99  --sat_fm_restart_options                ""
% 3.48/0.99  --sat_gr_def                            false
% 3.48/0.99  --sat_epr_types                         true
% 3.48/0.99  --sat_non_cyclic_types                  false
% 3.48/0.99  --sat_finite_models                     false
% 3.48/0.99  --sat_fm_lemmas                         false
% 3.48/0.99  --sat_fm_prep                           false
% 3.48/0.99  --sat_fm_uc_incr                        true
% 3.48/0.99  --sat_out_model                         small
% 3.48/0.99  --sat_out_clauses                       false
% 3.48/0.99  
% 3.48/0.99  ------ QBF Options
% 3.48/0.99  
% 3.48/0.99  --qbf_mode                              false
% 3.48/0.99  --qbf_elim_univ                         false
% 3.48/0.99  --qbf_dom_inst                          none
% 3.48/0.99  --qbf_dom_pre_inst                      false
% 3.48/0.99  --qbf_sk_in                             false
% 3.48/0.99  --qbf_pred_elim                         true
% 3.48/0.99  --qbf_split                             512
% 3.48/0.99  
% 3.48/0.99  ------ BMC1 Options
% 3.48/0.99  
% 3.48/0.99  --bmc1_incremental                      false
% 3.48/0.99  --bmc1_axioms                           reachable_all
% 3.48/0.99  --bmc1_min_bound                        0
% 3.48/0.99  --bmc1_max_bound                        -1
% 3.48/0.99  --bmc1_max_bound_default                -1
% 3.48/0.99  --bmc1_symbol_reachability              true
% 3.48/0.99  --bmc1_property_lemmas                  false
% 3.48/0.99  --bmc1_k_induction                      false
% 3.48/0.99  --bmc1_non_equiv_states                 false
% 3.48/0.99  --bmc1_deadlock                         false
% 3.48/0.99  --bmc1_ucm                              false
% 3.48/0.99  --bmc1_add_unsat_core                   none
% 3.48/0.99  --bmc1_unsat_core_children              false
% 3.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/0.99  --bmc1_out_stat                         full
% 3.48/0.99  --bmc1_ground_init                      false
% 3.48/0.99  --bmc1_pre_inst_next_state              false
% 3.48/0.99  --bmc1_pre_inst_state                   false
% 3.48/0.99  --bmc1_pre_inst_reach_state             false
% 3.48/0.99  --bmc1_out_unsat_core                   false
% 3.48/0.99  --bmc1_aig_witness_out                  false
% 3.48/0.99  --bmc1_verbose                          false
% 3.48/0.99  --bmc1_dump_clauses_tptp                false
% 3.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.48/0.99  --bmc1_dump_file                        -
% 3.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.48/0.99  --bmc1_ucm_extend_mode                  1
% 3.48/0.99  --bmc1_ucm_init_mode                    2
% 3.48/0.99  --bmc1_ucm_cone_mode                    none
% 3.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.48/0.99  --bmc1_ucm_relax_model                  4
% 3.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/0.99  --bmc1_ucm_layered_model                none
% 3.48/0.99  --bmc1_ucm_max_lemma_size               10
% 3.48/0.99  
% 3.48/0.99  ------ AIG Options
% 3.48/0.99  
% 3.48/0.99  --aig_mode                              false
% 3.48/0.99  
% 3.48/0.99  ------ Instantiation Options
% 3.48/0.99  
% 3.48/0.99  --instantiation_flag                    true
% 3.48/0.99  --inst_sos_flag                         false
% 3.48/0.99  --inst_sos_phase                        true
% 3.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel_side                     num_symb
% 3.48/0.99  --inst_solver_per_active                1400
% 3.48/0.99  --inst_solver_calls_frac                1.
% 3.48/0.99  --inst_passive_queue_type               priority_queues
% 3.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/0.99  --inst_passive_queues_freq              [25;2]
% 3.48/0.99  --inst_dismatching                      true
% 3.48/0.99  --inst_eager_unprocessed_to_passive     true
% 3.48/0.99  --inst_prop_sim_given                   true
% 3.48/0.99  --inst_prop_sim_new                     false
% 3.48/0.99  --inst_subs_new                         false
% 3.48/0.99  --inst_eq_res_simp                      false
% 3.48/0.99  --inst_subs_given                       false
% 3.48/0.99  --inst_orphan_elimination               true
% 3.48/0.99  --inst_learning_loop_flag               true
% 3.48/0.99  --inst_learning_start                   3000
% 3.48/0.99  --inst_learning_factor                  2
% 3.48/0.99  --inst_start_prop_sim_after_learn       3
% 3.48/0.99  --inst_sel_renew                        solver
% 3.48/0.99  --inst_lit_activity_flag                true
% 3.48/0.99  --inst_restr_to_given                   false
% 3.48/0.99  --inst_activity_threshold               500
% 3.48/0.99  --inst_out_proof                        true
% 3.48/0.99  
% 3.48/0.99  ------ Resolution Options
% 3.48/0.99  
% 3.48/0.99  --resolution_flag                       true
% 3.48/0.99  --res_lit_sel                           adaptive
% 3.48/0.99  --res_lit_sel_side                      none
% 3.48/0.99  --res_ordering                          kbo
% 3.48/0.99  --res_to_prop_solver                    active
% 3.48/0.99  --res_prop_simpl_new                    false
% 3.48/0.99  --res_prop_simpl_given                  true
% 3.48/0.99  --res_passive_queue_type                priority_queues
% 3.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/0.99  --res_passive_queues_freq               [15;5]
% 3.48/0.99  --res_forward_subs                      full
% 3.48/0.99  --res_backward_subs                     full
% 3.48/0.99  --res_forward_subs_resolution           true
% 3.48/0.99  --res_backward_subs_resolution          true
% 3.48/0.99  --res_orphan_elimination                true
% 3.48/0.99  --res_time_limit                        2.
% 3.48/0.99  --res_out_proof                         true
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Options
% 3.48/0.99  
% 3.48/0.99  --superposition_flag                    true
% 3.48/0.99  --sup_passive_queue_type                priority_queues
% 3.48/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/0.99  --sup_passive_queues_freq               [1;4]
% 3.48/0.99  --demod_completeness_check              fast
% 3.48/0.99  --demod_use_ground                      true
% 3.48/0.99  --sup_to_prop_solver                    passive
% 3.48/0.99  --sup_prop_simpl_new                    true
% 3.48/0.99  --sup_prop_simpl_given                  true
% 3.48/0.99  --sup_fun_splitting                     false
% 3.48/0.99  --sup_smt_interval                      50000
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Simplification Setup
% 3.48/0.99  
% 3.48/0.99  --sup_indices_passive                   []
% 3.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_full_bw                           [BwDemod]
% 3.48/0.99  --sup_immed_triv                        [TrivRules]
% 3.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_immed_bw_main                     []
% 3.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  
% 3.48/0.99  ------ Combination Options
% 3.48/0.99  
% 3.48/0.99  --comb_res_mult                         3
% 3.48/0.99  --comb_sup_mult                         2
% 3.48/0.99  --comb_inst_mult                        10
% 3.48/0.99  
% 3.48/0.99  ------ Debug Options
% 3.48/0.99  
% 3.48/0.99  --dbg_backtrace                         false
% 3.48/0.99  --dbg_dump_prop_clauses                 false
% 3.48/0.99  --dbg_dump_prop_clauses_file            -
% 3.48/0.99  --dbg_out_stat                          false
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  % SZS status Theorem for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  fof(f2,axiom,(
% 3.48/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f25,plain,(
% 3.48/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.48/0.99    inference(nnf_transformation,[],[f2])).
% 3.48/0.99  
% 3.48/0.99  fof(f26,plain,(
% 3.48/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.48/0.99    inference(flattening,[],[f25])).
% 3.48/0.99  
% 3.48/0.99  fof(f37,plain,(
% 3.48/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.48/0.99    inference(cnf_transformation,[],[f26])).
% 3.48/0.99  
% 3.48/0.99  fof(f70,plain,(
% 3.48/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.48/0.99    inference(equality_resolution,[],[f37])).
% 3.48/0.99  
% 3.48/0.99  fof(f8,axiom,(
% 3.48/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f27,plain,(
% 3.48/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.48/0.99    inference(nnf_transformation,[],[f8])).
% 3.48/0.99  
% 3.48/0.99  fof(f28,plain,(
% 3.48/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.48/0.99    inference(rectify,[],[f27])).
% 3.48/0.99  
% 3.48/0.99  fof(f29,plain,(
% 3.48/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f30,plain,(
% 3.48/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.48/0.99  
% 3.48/0.99  fof(f47,plain,(
% 3.48/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.48/0.99    inference(cnf_transformation,[],[f30])).
% 3.48/0.99  
% 3.48/0.99  fof(f71,plain,(
% 3.48/0.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.48/0.99    inference(equality_resolution,[],[f47])).
% 3.48/0.99  
% 3.48/0.99  fof(f9,axiom,(
% 3.48/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f20,plain,(
% 3.48/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f9])).
% 3.48/0.99  
% 3.48/0.99  fof(f31,plain,(
% 3.48/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.48/0.99    inference(nnf_transformation,[],[f20])).
% 3.48/0.99  
% 3.48/0.99  fof(f51,plain,(
% 3.48/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f31])).
% 3.48/0.99  
% 3.48/0.99  fof(f13,axiom,(
% 3.48/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f57,plain,(
% 3.48/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f13])).
% 3.48/0.99  
% 3.48/0.99  fof(f11,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f21,plain,(
% 3.48/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f11])).
% 3.48/0.99  
% 3.48/0.99  fof(f55,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f21])).
% 3.48/0.99  
% 3.48/0.99  fof(f3,axiom,(
% 3.48/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f40,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f3])).
% 3.48/0.99  
% 3.48/0.99  fof(f66,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f55,f40])).
% 3.48/0.99  
% 3.48/0.99  fof(f5,axiom,(
% 3.48/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f43,plain,(
% 3.48/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f5])).
% 3.48/0.99  
% 3.48/0.99  fof(f6,axiom,(
% 3.48/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f44,plain,(
% 3.48/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.48/0.99    inference(cnf_transformation,[],[f6])).
% 3.48/0.99  
% 3.48/0.99  fof(f64,plain,(
% 3.48/0.99    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.48/0.99    inference(definition_unfolding,[],[f44,f40])).
% 3.48/0.99  
% 3.48/0.99  fof(f14,axiom,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f23,plain,(
% 3.48/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f14])).
% 3.48/0.99  
% 3.48/0.99  fof(f58,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f23])).
% 3.48/0.99  
% 3.48/0.99  fof(f1,axiom,(
% 3.48/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f36,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f1])).
% 3.48/0.99  
% 3.48/0.99  fof(f7,axiom,(
% 3.48/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f18,plain,(
% 3.48/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.48/0.99    inference(ennf_transformation,[],[f7])).
% 3.48/0.99  
% 3.48/0.99  fof(f19,plain,(
% 3.48/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 3.48/0.99    inference(flattening,[],[f18])).
% 3.48/0.99  
% 3.48/0.99  fof(f45,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f19])).
% 3.48/0.99  
% 3.48/0.99  fof(f65,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.48/0.99    inference(definition_unfolding,[],[f45,f40])).
% 3.48/0.99  
% 3.48/0.99  fof(f15,conjecture,(
% 3.48/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f16,negated_conjecture,(
% 3.48/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.48/0.99    inference(negated_conjecture,[],[f15])).
% 3.48/0.99  
% 3.48/0.99  fof(f24,plain,(
% 3.48/0.99    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(ennf_transformation,[],[f16])).
% 3.48/0.99  
% 3.48/0.99  fof(f32,plain,(
% 3.48/0.99    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(nnf_transformation,[],[f24])).
% 3.48/0.99  
% 3.48/0.99  fof(f33,plain,(
% 3.48/0.99    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.48/0.99    inference(flattening,[],[f32])).
% 3.48/0.99  
% 3.48/0.99  fof(f34,plain,(
% 3.48/0.99    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f35,plain,(
% 3.48/0.99    (k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f33,f34])).
% 3.48/0.99  
% 3.48/0.99  fof(f60,plain,(
% 3.48/0.99    k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 3.48/0.99    inference(cnf_transformation,[],[f35])).
% 3.48/0.99  
% 3.48/0.99  fof(f10,axiom,(
% 3.48/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f54,plain,(
% 3.48/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f10])).
% 3.48/0.99  
% 3.48/0.99  fof(f68,plain,(
% 3.48/0.99    k1_xboole_0 = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 3.48/0.99    inference(definition_unfolding,[],[f60,f54])).
% 3.48/0.99  
% 3.48/0.99  fof(f59,plain,(
% 3.48/0.99    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.48/0.99    inference(cnf_transformation,[],[f35])).
% 3.48/0.99  
% 3.48/0.99  fof(f4,axiom,(
% 3.48/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f17,plain,(
% 3.48/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.48/0.99    inference(ennf_transformation,[],[f4])).
% 3.48/0.99  
% 3.48/0.99  fof(f42,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f17])).
% 3.48/0.99  
% 3.48/0.99  fof(f62,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f42,f40])).
% 3.48/0.99  
% 3.48/0.99  fof(f39,plain,(
% 3.48/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f26])).
% 3.48/0.99  
% 3.48/0.99  fof(f50,plain,(
% 3.48/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f31])).
% 3.48/0.99  
% 3.48/0.99  fof(f46,plain,(
% 3.48/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.48/0.99    inference(cnf_transformation,[],[f30])).
% 3.48/0.99  
% 3.48/0.99  fof(f72,plain,(
% 3.48/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.48/0.99    inference(equality_resolution,[],[f46])).
% 3.48/0.99  
% 3.48/0.99  fof(f61,plain,(
% 3.48/0.99    k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 3.48/0.99    inference(cnf_transformation,[],[f35])).
% 3.48/0.99  
% 3.48/0.99  fof(f67,plain,(
% 3.48/0.99    k1_xboole_0 != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 3.48/0.99    inference(definition_unfolding,[],[f61,f54])).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3,plain,
% 3.48/0.99      ( r1_tarski(X0,X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_926,plain,
% 3.48/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_11,plain,
% 3.48/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_919,plain,
% 3.48/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.48/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_15,plain,
% 3.48/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_915,plain,
% 3.48/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.48/0.99      | r2_hidden(X0,X1) != iProver_top
% 3.48/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2285,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.48/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.48/0.99      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_919,c_915]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_19,plain,
% 3.48/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_911,plain,
% 3.48/0.99      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4642,plain,
% 3.48/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.48/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.48/0.99      inference(forward_subsumption_resolution,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_2285,c_911]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_17,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_913,plain,
% 3.48/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4649,plain,
% 3.48/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 3.48/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_4642,c_913]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5658,plain,
% 3.48/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_926,c_4649]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_923,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5660,plain,
% 3.48/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_923,c_4649]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7,plain,
% 3.48/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5689,plain,
% 3.48/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_5660,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_20,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.48/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_910,plain,
% 3.48/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.48/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4650,plain,
% 3.48/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.48/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_4642,c_910]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4865,plain,
% 3.48/0.99      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_923,c_4650]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5917,plain,
% 3.48/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_5689,c_4865]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6186,plain,
% 3.48/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_5658,c_5917]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_0,plain,
% 3.48/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8,plain,
% 3.48/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.48/0.99      | ~ r1_tarski(X0,X2)
% 3.48/0.99      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.48/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_922,plain,
% 3.48/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.48/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.48/0.99      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2972,plain,
% 3.48/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.48/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.48/0.99      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_0,c_922]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6195,plain,
% 3.48/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.48/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.48/0.99      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_6186,c_2972]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6215,plain,
% 3.48/0.99      ( r1_xboole_0(sK2,sK2) != iProver_top
% 3.48/0.99      | r1_tarski(sK2,sK2) != iProver_top
% 3.48/0.99      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_6195]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_22,negated_conjecture,
% 3.48/0.99      ( r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 = sK2 ),
% 3.48/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_908,plain,
% 3.48/0.99      ( k1_xboole_0 = sK2
% 3.48/0.99      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_23,negated_conjecture,
% 3.48/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_907,plain,
% 3.48/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2155,plain,
% 3.48/0.99      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_907,c_913]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4,plain,
% 3.48/0.99      ( r1_xboole_0(X0,X1)
% 3.48/0.99      | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.48/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_925,plain,
% 3.48/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.48/0.99      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3866,plain,
% 3.48/0.99      ( r1_xboole_0(X0,sK2) = iProver_top
% 3.48/0.99      | r1_tarski(X0,k3_subset_1(sK1,sK2)) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2155,c_925]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4681,plain,
% 3.48/0.99      ( sK2 = k1_xboole_0 | r1_xboole_0(sK2,sK2) = iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_908,c_3866]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_416,plain,( X0 = X0 ),theory(equality) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1226,plain,
% 3.48/0.99      ( k3_subset_1(sK1,sK2) = k3_subset_1(sK1,sK2) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_416]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_419,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.48/0.99      theory(equality) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1172,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1)
% 3.48/0.99      | r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 3.48/0.99      | k3_subset_1(sK1,sK2) != X1
% 3.48/0.99      | sK2 != X0 ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_419]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1225,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,k3_subset_1(sK1,sK2))
% 3.48/0.99      | r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 3.48/0.99      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
% 3.48/0.99      | sK2 != X0 ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_1172]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1366,plain,
% 3.48/0.99      ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 3.48/0.99      | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2))
% 3.48/0.99      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
% 3.48/0.99      | sK2 != k1_xboole_0 ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_1225]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1368,plain,
% 3.48/0.99      ( k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
% 3.48/0.99      | sK2 != k1_xboole_0
% 3.48/0.99      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top
% 3.48/0.99      | r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_1366]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1367,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1370,plain,
% 3.48/0.99      ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_1367]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3894,plain,
% 3.48/0.99      ( r1_xboole_0(sK2,sK2) = iProver_top
% 3.48/0.99      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_3866]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4855,plain,
% 3.48/0.99      ( r1_xboole_0(sK2,sK2) = iProver_top ),
% 3.48/0.99      inference(global_propositional_subsumption,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_4681,c_1226,c_1368,c_1370,c_3894]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3865,plain,
% 3.48/0.99      ( r1_xboole_0(X0,sK2) != iProver_top
% 3.48/0.99      | r1_tarski(X0,k3_subset_1(sK1,sK2)) = iProver_top
% 3.48/0.99      | r1_tarski(X0,sK1) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2155,c_922]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3891,plain,
% 3.48/0.99      ( r1_xboole_0(sK2,sK2) != iProver_top
% 3.48/0.99      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top
% 3.48/0.99      | r1_tarski(sK2,sK1) != iProver_top ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_3865]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1,plain,
% 3.48/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.48/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_927,plain,
% 3.48/0.99      ( X0 = X1
% 3.48/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.48/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2417,plain,
% 3.48/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_923,c_927]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2430,plain,
% 3.48/0.99      ( k1_xboole_0 = sK2 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_2417]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_16,plain,
% 3.48/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1390,plain,
% 3.48/0.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_16,c_23]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1109,plain,
% 3.48/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 3.48/0.99      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 3.48/0.99      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1352,plain,
% 3.48/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1536,plain,
% 3.48/0.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 3.48/0.99      inference(global_propositional_subsumption,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_1390,c_23,c_1109,c_1352]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_12,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1736,plain,
% 3.48/0.99      ( r1_tarski(sK2,sK1) ),
% 3.48/0.99      inference(resolution,[status(thm)],[c_1536,c_12]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1737,plain,
% 3.48/0.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_1736]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_74,plain,
% 3.48/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_76,plain,
% 3.48/0.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_74]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_21,negated_conjecture,
% 3.48/0.99      ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 != sK2 ),
% 3.48/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_26,plain,
% 3.48/0.99      ( k1_xboole_0 != sK2
% 3.48/0.99      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(contradiction,plain,
% 3.48/0.99      ( $false ),
% 3.48/0.99      inference(minisat,
% 3.48/0.99                [status(thm)],
% 3.48/0.99                [c_6215,c_4855,c_3891,c_2430,c_1737,c_76,c_26]) ).
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  ------                               Statistics
% 3.48/0.99  
% 3.48/0.99  ------ Selected
% 3.48/0.99  
% 3.48/0.99  total_time:                             0.151
% 3.48/0.99  
%------------------------------------------------------------------------------
