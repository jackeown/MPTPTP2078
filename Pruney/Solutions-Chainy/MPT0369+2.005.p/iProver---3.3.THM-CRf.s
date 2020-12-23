%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:57 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 162 expanded)
%              Number of clauses        :   48 (  51 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  254 ( 516 expanded)
%              Number of equality atoms :   90 ( 140 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK2,k3_subset_1(X0,X1))
        & ~ r2_hidden(sK2,X1)
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ? [X2] :
            ( ~ r2_hidden(X2,k3_subset_1(X0,sK1))
            & ~ r2_hidden(X2,sK1)
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(X0)) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(sK0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(sK0)) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1))
    & ~ r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f32,f31,f30])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f52,f47])).

fof(f62,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f48,f61])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_701,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_705,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_706,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1263,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_705,c_706])).

cnf(c_12,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1271,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1263,c_12])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X0,k3_subset_1(X1,X2))
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | X0 != X3
    | k3_subset_1(X1,X2) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X2,X0)
    | k3_subset_1(X1,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X3
    | X0 != X4
    | k3_subset_1(X1,X0) != k1_xboole_0
    | k3_xboole_0(X3,X4) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_237])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X2) != k1_xboole_0
    | k3_xboole_0(X0,X2) = X0 ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_700,plain,
    ( k3_subset_1(X0,X1) != k1_xboole_0
    | k3_xboole_0(X2,X1) = X2
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_1390,plain,
    ( k3_xboole_0(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1271,c_700])).

cnf(c_14,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_707,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_734,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_707,c_12])).

cnf(c_3145,plain,
    ( k3_xboole_0(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1390,c_734])).

cnf(c_3149,plain,
    ( k3_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_701,c_3145])).

cnf(c_3380,plain,
    ( k3_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_0,c_3149])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_708,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1487,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_701,c_708])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_715,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1979,plain,
    ( r2_hidden(X0,k3_subset_1(sK0,sK1)) = iProver_top
    | r2_hidden(X0,k3_xboole_0(sK0,sK1)) = iProver_top
    | r2_hidden(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_715])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_704,plain,
    ( r2_hidden(sK2,k3_subset_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2435,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1)) = iProver_top
    | r2_hidden(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1979,c_704])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_843,plain,
    ( ~ v1_xboole_0(sK0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_844,plain,
    ( k1_xboole_0 = sK0
    | v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_859,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_860,plain,
    ( m1_subset_1(sK2,sK0) != iProver_top
    | r2_hidden(sK2,sK0) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_2523,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2435,c_23,c_25,c_844,c_860])).

cnf(c_3526,plain,
    ( r2_hidden(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3380,c_2523])).

cnf(c_20,negated_conjecture,
    ( ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,plain,
    ( r2_hidden(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3526,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : iproveropt_run.sh %d %s
% 0.09/0.28  % Computer   : n022.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.28  % CPULimit   : 60
% 0.09/0.28  % WCLimit    : 600
% 0.09/0.28  % DateTime   : Tue Dec  1 17:16:40 EST 2020
% 0.09/0.28  % CPUTime    : 
% 0.09/0.29  % Running in FOF mode
% 1.99/0.90  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/0.90  
% 1.99/0.90  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/0.90  
% 1.99/0.90  ------  iProver source info
% 1.99/0.90  
% 1.99/0.90  git: date: 2020-06-30 10:37:57 +0100
% 1.99/0.90  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/0.90  git: non_committed_changes: false
% 1.99/0.90  git: last_make_outside_of_git: false
% 1.99/0.90  
% 1.99/0.90  ------ 
% 1.99/0.90  
% 1.99/0.90  ------ Input Options
% 1.99/0.90  
% 1.99/0.90  --out_options                           all
% 1.99/0.90  --tptp_safe_out                         true
% 1.99/0.90  --problem_path                          ""
% 1.99/0.90  --include_path                          ""
% 1.99/0.90  --clausifier                            res/vclausify_rel
% 1.99/0.90  --clausifier_options                    --mode clausify
% 1.99/0.90  --stdin                                 false
% 1.99/0.90  --stats_out                             all
% 1.99/0.90  
% 1.99/0.90  ------ General Options
% 1.99/0.90  
% 1.99/0.90  --fof                                   false
% 1.99/0.90  --time_out_real                         305.
% 1.99/0.90  --time_out_virtual                      -1.
% 1.99/0.90  --symbol_type_check                     false
% 1.99/0.90  --clausify_out                          false
% 1.99/0.90  --sig_cnt_out                           false
% 1.99/0.90  --trig_cnt_out                          false
% 1.99/0.90  --trig_cnt_out_tolerance                1.
% 1.99/0.90  --trig_cnt_out_sk_spl                   false
% 1.99/0.90  --abstr_cl_out                          false
% 1.99/0.90  
% 1.99/0.90  ------ Global Options
% 1.99/0.90  
% 1.99/0.90  --schedule                              default
% 1.99/0.90  --add_important_lit                     false
% 1.99/0.90  --prop_solver_per_cl                    1000
% 1.99/0.90  --min_unsat_core                        false
% 1.99/0.90  --soft_assumptions                      false
% 1.99/0.90  --soft_lemma_size                       3
% 1.99/0.90  --prop_impl_unit_size                   0
% 1.99/0.90  --prop_impl_unit                        []
% 1.99/0.90  --share_sel_clauses                     true
% 1.99/0.90  --reset_solvers                         false
% 1.99/0.90  --bc_imp_inh                            [conj_cone]
% 1.99/0.90  --conj_cone_tolerance                   3.
% 1.99/0.90  --extra_neg_conj                        none
% 1.99/0.90  --large_theory_mode                     true
% 1.99/0.90  --prolific_symb_bound                   200
% 1.99/0.90  --lt_threshold                          2000
% 1.99/0.90  --clause_weak_htbl                      true
% 1.99/0.90  --gc_record_bc_elim                     false
% 1.99/0.90  
% 1.99/0.90  ------ Preprocessing Options
% 1.99/0.90  
% 1.99/0.90  --preprocessing_flag                    true
% 1.99/0.90  --time_out_prep_mult                    0.1
% 1.99/0.90  --splitting_mode                        input
% 1.99/0.90  --splitting_grd                         true
% 1.99/0.90  --splitting_cvd                         false
% 1.99/0.90  --splitting_cvd_svl                     false
% 1.99/0.90  --splitting_nvd                         32
% 1.99/0.90  --sub_typing                            true
% 1.99/0.90  --prep_gs_sim                           true
% 1.99/0.90  --prep_unflatten                        true
% 1.99/0.90  --prep_res_sim                          true
% 1.99/0.90  --prep_upred                            true
% 1.99/0.90  --prep_sem_filter                       exhaustive
% 1.99/0.90  --prep_sem_filter_out                   false
% 1.99/0.90  --pred_elim                             true
% 1.99/0.90  --res_sim_input                         true
% 1.99/0.90  --eq_ax_congr_red                       true
% 1.99/0.90  --pure_diseq_elim                       true
% 1.99/0.90  --brand_transform                       false
% 1.99/0.90  --non_eq_to_eq                          false
% 1.99/0.90  --prep_def_merge                        true
% 1.99/0.90  --prep_def_merge_prop_impl              false
% 1.99/0.90  --prep_def_merge_mbd                    true
% 1.99/0.90  --prep_def_merge_tr_red                 false
% 1.99/0.90  --prep_def_merge_tr_cl                  false
% 1.99/0.90  --smt_preprocessing                     true
% 1.99/0.90  --smt_ac_axioms                         fast
% 1.99/0.90  --preprocessed_out                      false
% 1.99/0.90  --preprocessed_stats                    false
% 1.99/0.90  
% 1.99/0.90  ------ Abstraction refinement Options
% 1.99/0.90  
% 1.99/0.90  --abstr_ref                             []
% 1.99/0.90  --abstr_ref_prep                        false
% 1.99/0.90  --abstr_ref_until_sat                   false
% 1.99/0.90  --abstr_ref_sig_restrict                funpre
% 1.99/0.90  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.90  --abstr_ref_under                       []
% 1.99/0.90  
% 1.99/0.90  ------ SAT Options
% 1.99/0.90  
% 1.99/0.90  --sat_mode                              false
% 1.99/0.90  --sat_fm_restart_options                ""
% 1.99/0.90  --sat_gr_def                            false
% 1.99/0.90  --sat_epr_types                         true
% 1.99/0.90  --sat_non_cyclic_types                  false
% 1.99/0.90  --sat_finite_models                     false
% 1.99/0.90  --sat_fm_lemmas                         false
% 1.99/0.90  --sat_fm_prep                           false
% 1.99/0.90  --sat_fm_uc_incr                        true
% 1.99/0.90  --sat_out_model                         small
% 1.99/0.90  --sat_out_clauses                       false
% 1.99/0.90  
% 1.99/0.90  ------ QBF Options
% 1.99/0.90  
% 1.99/0.90  --qbf_mode                              false
% 1.99/0.90  --qbf_elim_univ                         false
% 1.99/0.90  --qbf_dom_inst                          none
% 1.99/0.90  --qbf_dom_pre_inst                      false
% 1.99/0.90  --qbf_sk_in                             false
% 1.99/0.90  --qbf_pred_elim                         true
% 1.99/0.90  --qbf_split                             512
% 1.99/0.90  
% 1.99/0.90  ------ BMC1 Options
% 1.99/0.90  
% 1.99/0.90  --bmc1_incremental                      false
% 1.99/0.90  --bmc1_axioms                           reachable_all
% 1.99/0.90  --bmc1_min_bound                        0
% 1.99/0.90  --bmc1_max_bound                        -1
% 1.99/0.90  --bmc1_max_bound_default                -1
% 1.99/0.90  --bmc1_symbol_reachability              true
% 1.99/0.90  --bmc1_property_lemmas                  false
% 1.99/0.90  --bmc1_k_induction                      false
% 1.99/0.90  --bmc1_non_equiv_states                 false
% 1.99/0.90  --bmc1_deadlock                         false
% 1.99/0.90  --bmc1_ucm                              false
% 1.99/0.90  --bmc1_add_unsat_core                   none
% 1.99/0.90  --bmc1_unsat_core_children              false
% 1.99/0.90  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.90  --bmc1_out_stat                         full
% 1.99/0.90  --bmc1_ground_init                      false
% 1.99/0.90  --bmc1_pre_inst_next_state              false
% 1.99/0.90  --bmc1_pre_inst_state                   false
% 1.99/0.90  --bmc1_pre_inst_reach_state             false
% 1.99/0.90  --bmc1_out_unsat_core                   false
% 1.99/0.90  --bmc1_aig_witness_out                  false
% 1.99/0.90  --bmc1_verbose                          false
% 1.99/0.90  --bmc1_dump_clauses_tptp                false
% 1.99/0.90  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.90  --bmc1_dump_file                        -
% 1.99/0.90  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.90  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.90  --bmc1_ucm_extend_mode                  1
% 1.99/0.90  --bmc1_ucm_init_mode                    2
% 1.99/0.90  --bmc1_ucm_cone_mode                    none
% 1.99/0.90  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.90  --bmc1_ucm_relax_model                  4
% 1.99/0.90  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.90  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.90  --bmc1_ucm_layered_model                none
% 1.99/0.90  --bmc1_ucm_max_lemma_size               10
% 1.99/0.90  
% 1.99/0.90  ------ AIG Options
% 1.99/0.90  
% 1.99/0.90  --aig_mode                              false
% 1.99/0.90  
% 1.99/0.90  ------ Instantiation Options
% 1.99/0.90  
% 1.99/0.90  --instantiation_flag                    true
% 1.99/0.90  --inst_sos_flag                         false
% 1.99/0.90  --inst_sos_phase                        true
% 1.99/0.90  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.90  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.90  --inst_lit_sel_side                     num_symb
% 1.99/0.90  --inst_solver_per_active                1400
% 1.99/0.90  --inst_solver_calls_frac                1.
% 1.99/0.90  --inst_passive_queue_type               priority_queues
% 1.99/0.90  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.90  --inst_passive_queues_freq              [25;2]
% 1.99/0.90  --inst_dismatching                      true
% 1.99/0.90  --inst_eager_unprocessed_to_passive     true
% 1.99/0.90  --inst_prop_sim_given                   true
% 1.99/0.90  --inst_prop_sim_new                     false
% 1.99/0.90  --inst_subs_new                         false
% 1.99/0.90  --inst_eq_res_simp                      false
% 1.99/0.90  --inst_subs_given                       false
% 1.99/0.90  --inst_orphan_elimination               true
% 1.99/0.90  --inst_learning_loop_flag               true
% 1.99/0.90  --inst_learning_start                   3000
% 1.99/0.90  --inst_learning_factor                  2
% 1.99/0.90  --inst_start_prop_sim_after_learn       3
% 1.99/0.90  --inst_sel_renew                        solver
% 1.99/0.90  --inst_lit_activity_flag                true
% 1.99/0.90  --inst_restr_to_given                   false
% 1.99/0.90  --inst_activity_threshold               500
% 1.99/0.90  --inst_out_proof                        true
% 1.99/0.90  
% 1.99/0.90  ------ Resolution Options
% 1.99/0.90  
% 1.99/0.90  --resolution_flag                       true
% 1.99/0.90  --res_lit_sel                           adaptive
% 1.99/0.90  --res_lit_sel_side                      none
% 1.99/0.90  --res_ordering                          kbo
% 1.99/0.90  --res_to_prop_solver                    active
% 1.99/0.90  --res_prop_simpl_new                    false
% 1.99/0.90  --res_prop_simpl_given                  true
% 1.99/0.90  --res_passive_queue_type                priority_queues
% 1.99/0.90  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.90  --res_passive_queues_freq               [15;5]
% 1.99/0.90  --res_forward_subs                      full
% 1.99/0.90  --res_backward_subs                     full
% 1.99/0.90  --res_forward_subs_resolution           true
% 1.99/0.90  --res_backward_subs_resolution          true
% 1.99/0.90  --res_orphan_elimination                true
% 1.99/0.90  --res_time_limit                        2.
% 1.99/0.90  --res_out_proof                         true
% 1.99/0.90  
% 1.99/0.90  ------ Superposition Options
% 1.99/0.90  
% 1.99/0.90  --superposition_flag                    true
% 1.99/0.90  --sup_passive_queue_type                priority_queues
% 1.99/0.90  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.90  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.90  --demod_completeness_check              fast
% 1.99/0.90  --demod_use_ground                      true
% 1.99/0.90  --sup_to_prop_solver                    passive
% 1.99/0.90  --sup_prop_simpl_new                    true
% 1.99/0.90  --sup_prop_simpl_given                  true
% 1.99/0.90  --sup_fun_splitting                     false
% 1.99/0.90  --sup_smt_interval                      50000
% 1.99/0.90  
% 1.99/0.90  ------ Superposition Simplification Setup
% 1.99/0.90  
% 1.99/0.90  --sup_indices_passive                   []
% 1.99/0.90  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.90  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.90  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.90  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.90  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.90  --sup_full_bw                           [BwDemod]
% 1.99/0.90  --sup_immed_triv                        [TrivRules]
% 1.99/0.90  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.90  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.90  --sup_immed_bw_main                     []
% 1.99/0.90  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.90  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.90  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.90  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.90  
% 1.99/0.90  ------ Combination Options
% 1.99/0.90  
% 1.99/0.90  --comb_res_mult                         3
% 1.99/0.90  --comb_sup_mult                         2
% 1.99/0.90  --comb_inst_mult                        10
% 1.99/0.90  
% 1.99/0.90  ------ Debug Options
% 1.99/0.90  
% 1.99/0.90  --dbg_backtrace                         false
% 1.99/0.90  --dbg_dump_prop_clauses                 false
% 1.99/0.90  --dbg_dump_prop_clauses_file            -
% 1.99/0.90  --dbg_out_stat                          false
% 1.99/0.90  ------ Parsing...
% 1.99/0.90  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/0.90  
% 1.99/0.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.99/0.90  
% 1.99/0.90  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/0.90  
% 1.99/0.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/0.90  ------ Proving...
% 1.99/0.90  ------ Problem Properties 
% 1.99/0.90  
% 1.99/0.90  
% 1.99/0.90  clauses                                 21
% 1.99/0.90  conjectures                             5
% 1.99/0.90  EPR                                     8
% 1.99/0.90  Horn                                    16
% 1.99/0.90  unary                                   9
% 1.99/0.90  binary                                  3
% 1.99/0.90  lits                                    43
% 1.99/0.90  lits eq                                 8
% 1.99/0.90  fd_pure                                 0
% 1.99/0.90  fd_pseudo                               0
% 1.99/0.90  fd_cond                                 1
% 1.99/0.90  fd_pseudo_cond                          0
% 1.99/0.90  AC symbols                              0
% 1.99/0.90  
% 1.99/0.90  ------ Schedule dynamic 5 is on 
% 1.99/0.90  
% 1.99/0.90  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/0.90  
% 1.99/0.90  
% 1.99/0.90  ------ 
% 1.99/0.90  Current options:
% 1.99/0.90  ------ 
% 1.99/0.90  
% 1.99/0.90  ------ Input Options
% 1.99/0.90  
% 1.99/0.90  --out_options                           all
% 1.99/0.90  --tptp_safe_out                         true
% 1.99/0.90  --problem_path                          ""
% 1.99/0.90  --include_path                          ""
% 1.99/0.90  --clausifier                            res/vclausify_rel
% 1.99/0.90  --clausifier_options                    --mode clausify
% 1.99/0.90  --stdin                                 false
% 1.99/0.90  --stats_out                             all
% 1.99/0.90  
% 1.99/0.90  ------ General Options
% 1.99/0.90  
% 1.99/0.90  --fof                                   false
% 1.99/0.90  --time_out_real                         305.
% 1.99/0.90  --time_out_virtual                      -1.
% 1.99/0.90  --symbol_type_check                     false
% 1.99/0.90  --clausify_out                          false
% 1.99/0.90  --sig_cnt_out                           false
% 1.99/0.90  --trig_cnt_out                          false
% 1.99/0.90  --trig_cnt_out_tolerance                1.
% 1.99/0.90  --trig_cnt_out_sk_spl                   false
% 1.99/0.90  --abstr_cl_out                          false
% 1.99/0.90  
% 1.99/0.90  ------ Global Options
% 1.99/0.90  
% 1.99/0.90  --schedule                              default
% 1.99/0.90  --add_important_lit                     false
% 1.99/0.90  --prop_solver_per_cl                    1000
% 1.99/0.90  --min_unsat_core                        false
% 1.99/0.90  --soft_assumptions                      false
% 1.99/0.90  --soft_lemma_size                       3
% 1.99/0.90  --prop_impl_unit_size                   0
% 1.99/0.90  --prop_impl_unit                        []
% 1.99/0.90  --share_sel_clauses                     true
% 1.99/0.90  --reset_solvers                         false
% 1.99/0.90  --bc_imp_inh                            [conj_cone]
% 1.99/0.90  --conj_cone_tolerance                   3.
% 1.99/0.90  --extra_neg_conj                        none
% 1.99/0.90  --large_theory_mode                     true
% 1.99/0.90  --prolific_symb_bound                   200
% 1.99/0.90  --lt_threshold                          2000
% 1.99/0.90  --clause_weak_htbl                      true
% 1.99/0.90  --gc_record_bc_elim                     false
% 1.99/0.90  
% 1.99/0.90  ------ Preprocessing Options
% 1.99/0.90  
% 1.99/0.90  --preprocessing_flag                    true
% 1.99/0.90  --time_out_prep_mult                    0.1
% 1.99/0.90  --splitting_mode                        input
% 1.99/0.90  --splitting_grd                         true
% 1.99/0.90  --splitting_cvd                         false
% 1.99/0.90  --splitting_cvd_svl                     false
% 1.99/0.90  --splitting_nvd                         32
% 1.99/0.90  --sub_typing                            true
% 1.99/0.90  --prep_gs_sim                           true
% 1.99/0.90  --prep_unflatten                        true
% 1.99/0.90  --prep_res_sim                          true
% 1.99/0.90  --prep_upred                            true
% 1.99/0.90  --prep_sem_filter                       exhaustive
% 1.99/0.90  --prep_sem_filter_out                   false
% 1.99/0.90  --pred_elim                             true
% 1.99/0.90  --res_sim_input                         true
% 1.99/0.90  --eq_ax_congr_red                       true
% 1.99/0.90  --pure_diseq_elim                       true
% 1.99/0.90  --brand_transform                       false
% 1.99/0.90  --non_eq_to_eq                          false
% 1.99/0.90  --prep_def_merge                        true
% 1.99/0.90  --prep_def_merge_prop_impl              false
% 1.99/0.90  --prep_def_merge_mbd                    true
% 1.99/0.90  --prep_def_merge_tr_red                 false
% 1.99/0.90  --prep_def_merge_tr_cl                  false
% 1.99/0.90  --smt_preprocessing                     true
% 1.99/0.90  --smt_ac_axioms                         fast
% 1.99/0.90  --preprocessed_out                      false
% 1.99/0.90  --preprocessed_stats                    false
% 1.99/0.90  
% 1.99/0.90  ------ Abstraction refinement Options
% 1.99/0.90  
% 1.99/0.90  --abstr_ref                             []
% 1.99/0.90  --abstr_ref_prep                        false
% 1.99/0.90  --abstr_ref_until_sat                   false
% 1.99/0.90  --abstr_ref_sig_restrict                funpre
% 1.99/0.90  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.90  --abstr_ref_under                       []
% 1.99/0.90  
% 1.99/0.90  ------ SAT Options
% 1.99/0.90  
% 1.99/0.90  --sat_mode                              false
% 1.99/0.90  --sat_fm_restart_options                ""
% 1.99/0.90  --sat_gr_def                            false
% 1.99/0.90  --sat_epr_types                         true
% 1.99/0.90  --sat_non_cyclic_types                  false
% 1.99/0.90  --sat_finite_models                     false
% 1.99/0.90  --sat_fm_lemmas                         false
% 1.99/0.90  --sat_fm_prep                           false
% 1.99/0.90  --sat_fm_uc_incr                        true
% 1.99/0.90  --sat_out_model                         small
% 1.99/0.90  --sat_out_clauses                       false
% 1.99/0.90  
% 1.99/0.90  ------ QBF Options
% 1.99/0.90  
% 1.99/0.90  --qbf_mode                              false
% 1.99/0.90  --qbf_elim_univ                         false
% 1.99/0.90  --qbf_dom_inst                          none
% 1.99/0.90  --qbf_dom_pre_inst                      false
% 1.99/0.90  --qbf_sk_in                             false
% 1.99/0.90  --qbf_pred_elim                         true
% 1.99/0.90  --qbf_split                             512
% 1.99/0.90  
% 1.99/0.90  ------ BMC1 Options
% 1.99/0.90  
% 1.99/0.90  --bmc1_incremental                      false
% 1.99/0.90  --bmc1_axioms                           reachable_all
% 1.99/0.90  --bmc1_min_bound                        0
% 1.99/0.90  --bmc1_max_bound                        -1
% 1.99/0.90  --bmc1_max_bound_default                -1
% 1.99/0.90  --bmc1_symbol_reachability              true
% 1.99/0.90  --bmc1_property_lemmas                  false
% 1.99/0.90  --bmc1_k_induction                      false
% 1.99/0.90  --bmc1_non_equiv_states                 false
% 1.99/0.90  --bmc1_deadlock                         false
% 1.99/0.90  --bmc1_ucm                              false
% 1.99/0.90  --bmc1_add_unsat_core                   none
% 1.99/0.90  --bmc1_unsat_core_children              false
% 1.99/0.90  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.90  --bmc1_out_stat                         full
% 1.99/0.90  --bmc1_ground_init                      false
% 1.99/0.90  --bmc1_pre_inst_next_state              false
% 1.99/0.90  --bmc1_pre_inst_state                   false
% 1.99/0.90  --bmc1_pre_inst_reach_state             false
% 1.99/0.90  --bmc1_out_unsat_core                   false
% 1.99/0.90  --bmc1_aig_witness_out                  false
% 1.99/0.90  --bmc1_verbose                          false
% 1.99/0.90  --bmc1_dump_clauses_tptp                false
% 1.99/0.90  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.90  --bmc1_dump_file                        -
% 1.99/0.90  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.90  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.90  --bmc1_ucm_extend_mode                  1
% 1.99/0.90  --bmc1_ucm_init_mode                    2
% 1.99/0.90  --bmc1_ucm_cone_mode                    none
% 1.99/0.90  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.90  --bmc1_ucm_relax_model                  4
% 1.99/0.90  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.90  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.90  --bmc1_ucm_layered_model                none
% 1.99/0.90  --bmc1_ucm_max_lemma_size               10
% 1.99/0.90  
% 1.99/0.90  ------ AIG Options
% 1.99/0.90  
% 1.99/0.90  --aig_mode                              false
% 1.99/0.90  
% 1.99/0.90  ------ Instantiation Options
% 1.99/0.90  
% 1.99/0.90  --instantiation_flag                    true
% 1.99/0.90  --inst_sos_flag                         false
% 1.99/0.90  --inst_sos_phase                        true
% 1.99/0.90  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.90  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.90  --inst_lit_sel_side                     none
% 1.99/0.90  --inst_solver_per_active                1400
% 1.99/0.90  --inst_solver_calls_frac                1.
% 1.99/0.90  --inst_passive_queue_type               priority_queues
% 1.99/0.90  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.90  --inst_passive_queues_freq              [25;2]
% 1.99/0.90  --inst_dismatching                      true
% 1.99/0.90  --inst_eager_unprocessed_to_passive     true
% 1.99/0.90  --inst_prop_sim_given                   true
% 1.99/0.90  --inst_prop_sim_new                     false
% 1.99/0.90  --inst_subs_new                         false
% 1.99/0.90  --inst_eq_res_simp                      false
% 1.99/0.90  --inst_subs_given                       false
% 1.99/0.90  --inst_orphan_elimination               true
% 1.99/0.90  --inst_learning_loop_flag               true
% 1.99/0.90  --inst_learning_start                   3000
% 1.99/0.90  --inst_learning_factor                  2
% 1.99/0.90  --inst_start_prop_sim_after_learn       3
% 1.99/0.90  --inst_sel_renew                        solver
% 1.99/0.90  --inst_lit_activity_flag                true
% 1.99/0.90  --inst_restr_to_given                   false
% 1.99/0.90  --inst_activity_threshold               500
% 1.99/0.90  --inst_out_proof                        true
% 1.99/0.90  
% 1.99/0.90  ------ Resolution Options
% 1.99/0.90  
% 1.99/0.90  --resolution_flag                       false
% 1.99/0.90  --res_lit_sel                           adaptive
% 1.99/0.90  --res_lit_sel_side                      none
% 1.99/0.90  --res_ordering                          kbo
% 1.99/0.90  --res_to_prop_solver                    active
% 1.99/0.90  --res_prop_simpl_new                    false
% 1.99/0.90  --res_prop_simpl_given                  true
% 1.99/0.90  --res_passive_queue_type                priority_queues
% 1.99/0.90  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.90  --res_passive_queues_freq               [15;5]
% 1.99/0.90  --res_forward_subs                      full
% 1.99/0.90  --res_backward_subs                     full
% 1.99/0.90  --res_forward_subs_resolution           true
% 1.99/0.90  --res_backward_subs_resolution          true
% 1.99/0.90  --res_orphan_elimination                true
% 1.99/0.90  --res_time_limit                        2.
% 1.99/0.90  --res_out_proof                         true
% 1.99/0.90  
% 1.99/0.90  ------ Superposition Options
% 1.99/0.90  
% 1.99/0.90  --superposition_flag                    true
% 1.99/0.90  --sup_passive_queue_type                priority_queues
% 1.99/0.90  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.90  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.90  --demod_completeness_check              fast
% 1.99/0.90  --demod_use_ground                      true
% 1.99/0.90  --sup_to_prop_solver                    passive
% 1.99/0.90  --sup_prop_simpl_new                    true
% 1.99/0.90  --sup_prop_simpl_given                  true
% 1.99/0.90  --sup_fun_splitting                     false
% 1.99/0.90  --sup_smt_interval                      50000
% 1.99/0.90  
% 1.99/0.90  ------ Superposition Simplification Setup
% 1.99/0.90  
% 1.99/0.90  --sup_indices_passive                   []
% 1.99/0.90  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.90  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.90  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.90  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.90  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.90  --sup_full_bw                           [BwDemod]
% 1.99/0.90  --sup_immed_triv                        [TrivRules]
% 1.99/0.90  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.90  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.90  --sup_immed_bw_main                     []
% 1.99/0.90  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.90  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.90  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.90  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.90  
% 1.99/0.90  ------ Combination Options
% 1.99/0.90  
% 1.99/0.90  --comb_res_mult                         3
% 1.99/0.90  --comb_sup_mult                         2
% 1.99/0.90  --comb_inst_mult                        10
% 1.99/0.90  
% 1.99/0.90  ------ Debug Options
% 1.99/0.90  
% 1.99/0.90  --dbg_backtrace                         false
% 1.99/0.90  --dbg_dump_prop_clauses                 false
% 1.99/0.90  --dbg_dump_prop_clauses_file            -
% 1.99/0.90  --dbg_out_stat                          false
% 1.99/0.90  
% 1.99/0.90  
% 1.99/0.90  
% 1.99/0.90  
% 1.99/0.90  ------ Proving...
% 1.99/0.90  
% 1.99/0.90  
% 1.99/0.90  % SZS status Theorem for theBenchmark.p
% 1.99/0.90  
% 1.99/0.90  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/0.90  
% 1.99/0.90  fof(f1,axiom,(
% 1.99/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f34,plain,(
% 1.99/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.99/0.90    inference(cnf_transformation,[],[f1])).
% 1.99/0.90  
% 1.99/0.90  fof(f16,conjecture,(
% 1.99/0.90    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f17,negated_conjecture,(
% 1.99/0.90    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.99/0.90    inference(negated_conjecture,[],[f16])).
% 1.99/0.90  
% 1.99/0.90  fof(f25,plain,(
% 1.99/0.90    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.99/0.90    inference(ennf_transformation,[],[f17])).
% 1.99/0.90  
% 1.99/0.90  fof(f26,plain,(
% 1.99/0.90    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 1.99/0.90    inference(flattening,[],[f25])).
% 1.99/0.90  
% 1.99/0.90  fof(f32,plain,(
% 1.99/0.90    ( ! [X0,X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK2,k3_subset_1(X0,X1)) & ~r2_hidden(sK2,X1) & m1_subset_1(sK2,X0))) )),
% 1.99/0.90    introduced(choice_axiom,[])).
% 1.99/0.90  
% 1.99/0.90  fof(f31,plain,(
% 1.99/0.90    ( ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,sK1)) & ~r2_hidden(X2,sK1) & m1_subset_1(X2,X0)) & m1_subset_1(sK1,k1_zfmisc_1(X0)))) )),
% 1.99/0.90    introduced(choice_axiom,[])).
% 1.99/0.90  
% 1.99/0.90  fof(f30,plain,(
% 1.99/0.90    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0) => (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(sK0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0)),
% 1.99/0.90    introduced(choice_axiom,[])).
% 1.99/0.90  
% 1.99/0.90  fof(f33,plain,(
% 1.99/0.90    ((~r2_hidden(sK2,k3_subset_1(sK0,sK1)) & ~r2_hidden(sK2,sK1) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))) & k1_xboole_0 != sK0),
% 1.99/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f32,f31,f30])).
% 1.99/0.90  
% 1.99/0.90  fof(f57,plain,(
% 1.99/0.90    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.99/0.90    inference(cnf_transformation,[],[f33])).
% 1.99/0.90  
% 1.99/0.90  fof(f15,axiom,(
% 1.99/0.90    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f55,plain,(
% 1.99/0.90    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.99/0.90    inference(cnf_transformation,[],[f15])).
% 1.99/0.90  
% 1.99/0.90  fof(f12,axiom,(
% 1.99/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f23,plain,(
% 1.99/0.90    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.90    inference(ennf_transformation,[],[f12])).
% 1.99/0.90  
% 1.99/0.90  fof(f51,plain,(
% 1.99/0.90    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.90    inference(cnf_transformation,[],[f23])).
% 1.99/0.90  
% 1.99/0.90  fof(f9,axiom,(
% 1.99/0.90    ! [X0] : k2_subset_1(X0) = X0),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f48,plain,(
% 1.99/0.90    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.99/0.90    inference(cnf_transformation,[],[f9])).
% 1.99/0.90  
% 1.99/0.90  fof(f13,axiom,(
% 1.99/0.90    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f52,plain,(
% 1.99/0.90    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.99/0.90    inference(cnf_transformation,[],[f13])).
% 1.99/0.90  
% 1.99/0.90  fof(f8,axiom,(
% 1.99/0.90    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f47,plain,(
% 1.99/0.90    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.99/0.90    inference(cnf_transformation,[],[f8])).
% 1.99/0.90  
% 1.99/0.90  fof(f61,plain,(
% 1.99/0.90    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.99/0.90    inference(definition_unfolding,[],[f52,f47])).
% 1.99/0.90  
% 1.99/0.90  fof(f62,plain,(
% 1.99/0.90    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.99/0.90    inference(definition_unfolding,[],[f48,f61])).
% 1.99/0.90  
% 1.99/0.90  fof(f5,axiom,(
% 1.99/0.90    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f20,plain,(
% 1.99/0.90    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.99/0.90    inference(ennf_transformation,[],[f5])).
% 1.99/0.90  
% 1.99/0.90  fof(f41,plain,(
% 1.99/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.99/0.90    inference(cnf_transformation,[],[f20])).
% 1.99/0.90  
% 1.99/0.90  fof(f6,axiom,(
% 1.99/0.90    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f42,plain,(
% 1.99/0.90    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.99/0.90    inference(cnf_transformation,[],[f6])).
% 1.99/0.90  
% 1.99/0.90  fof(f14,axiom,(
% 1.99/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f24,plain,(
% 1.99/0.90    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.90    inference(ennf_transformation,[],[f14])).
% 1.99/0.90  
% 1.99/0.90  fof(f29,plain,(
% 1.99/0.90    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.90    inference(nnf_transformation,[],[f24])).
% 1.99/0.90  
% 1.99/0.90  fof(f53,plain,(
% 1.99/0.90    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.90    inference(cnf_transformation,[],[f29])).
% 1.99/0.90  
% 1.99/0.90  fof(f11,axiom,(
% 1.99/0.90    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f50,plain,(
% 1.99/0.90    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.99/0.90    inference(cnf_transformation,[],[f11])).
% 1.99/0.90  
% 1.99/0.90  fof(f64,plain,(
% 1.99/0.90    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.99/0.90    inference(definition_unfolding,[],[f50,f61])).
% 1.99/0.90  
% 1.99/0.90  fof(f10,axiom,(
% 1.99/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f22,plain,(
% 1.99/0.90    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.90    inference(ennf_transformation,[],[f10])).
% 1.99/0.90  
% 1.99/0.90  fof(f49,plain,(
% 1.99/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.90    inference(cnf_transformation,[],[f22])).
% 1.99/0.90  
% 1.99/0.90  fof(f4,axiom,(
% 1.99/0.90    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f40,plain,(
% 1.99/0.90    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 1.99/0.90    inference(cnf_transformation,[],[f4])).
% 1.99/0.90  
% 1.99/0.90  fof(f63,plain,(
% 1.99/0.90    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.90    inference(definition_unfolding,[],[f49,f40])).
% 1.99/0.90  
% 1.99/0.90  fof(f3,axiom,(
% 1.99/0.90    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f19,plain,(
% 1.99/0.90    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.99/0.90    inference(ennf_transformation,[],[f3])).
% 1.99/0.90  
% 1.99/0.90  fof(f27,plain,(
% 1.99/0.90    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.99/0.90    inference(nnf_transformation,[],[f19])).
% 1.99/0.90  
% 1.99/0.90  fof(f38,plain,(
% 1.99/0.90    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.99/0.90    inference(cnf_transformation,[],[f27])).
% 1.99/0.90  
% 1.99/0.90  fof(f60,plain,(
% 1.99/0.90    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 1.99/0.90    inference(cnf_transformation,[],[f33])).
% 1.99/0.90  
% 1.99/0.90  fof(f56,plain,(
% 1.99/0.90    k1_xboole_0 != sK0),
% 1.99/0.90    inference(cnf_transformation,[],[f33])).
% 1.99/0.90  
% 1.99/0.90  fof(f58,plain,(
% 1.99/0.90    m1_subset_1(sK2,sK0)),
% 1.99/0.90    inference(cnf_transformation,[],[f33])).
% 1.99/0.90  
% 1.99/0.90  fof(f2,axiom,(
% 1.99/0.90    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f18,plain,(
% 1.99/0.90    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.99/0.90    inference(ennf_transformation,[],[f2])).
% 1.99/0.90  
% 1.99/0.90  fof(f35,plain,(
% 1.99/0.90    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.99/0.90    inference(cnf_transformation,[],[f18])).
% 1.99/0.90  
% 1.99/0.90  fof(f7,axiom,(
% 1.99/0.90    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.99/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.90  
% 1.99/0.90  fof(f21,plain,(
% 1.99/0.90    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.99/0.90    inference(ennf_transformation,[],[f7])).
% 1.99/0.90  
% 1.99/0.90  fof(f28,plain,(
% 1.99/0.90    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.99/0.90    inference(nnf_transformation,[],[f21])).
% 1.99/0.90  
% 1.99/0.90  fof(f43,plain,(
% 1.99/0.90    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.99/0.90    inference(cnf_transformation,[],[f28])).
% 1.99/0.90  
% 1.99/0.90  fof(f59,plain,(
% 1.99/0.90    ~r2_hidden(sK2,sK1)),
% 1.99/0.90    inference(cnf_transformation,[],[f33])).
% 1.99/0.90  
% 1.99/0.90  cnf(c_0,plain,
% 1.99/0.90      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 1.99/0.90      inference(cnf_transformation,[],[f34]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_22,negated_conjecture,
% 1.99/0.90      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 1.99/0.90      inference(cnf_transformation,[],[f57]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_701,plain,
% 1.99/0.90      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_18,plain,
% 1.99/0.90      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.99/0.90      inference(cnf_transformation,[],[f55]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_705,plain,
% 1.99/0.90      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_15,plain,
% 1.99/0.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.90      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 1.99/0.90      inference(cnf_transformation,[],[f51]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_706,plain,
% 1.99/0.90      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 1.99/0.90      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_1263,plain,
% 1.99/0.90      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.99/0.90      inference(superposition,[status(thm)],[c_705,c_706]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_12,plain,
% 1.99/0.90      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 1.99/0.90      inference(cnf_transformation,[],[f62]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_1271,plain,
% 1.99/0.90      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 1.99/0.90      inference(light_normalisation,[status(thm)],[c_1263,c_12]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_6,plain,
% 1.99/0.90      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 1.99/0.90      inference(cnf_transformation,[],[f41]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_7,plain,
% 1.99/0.90      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.99/0.90      inference(cnf_transformation,[],[f42]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_17,plain,
% 1.99/0.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.90      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.99/0.90      | ~ r1_xboole_0(X0,k3_subset_1(X1,X2))
% 1.99/0.90      | r1_tarski(X0,X2) ),
% 1.99/0.90      inference(cnf_transformation,[],[f53]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_236,plain,
% 1.99/0.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.90      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.99/0.90      | r1_tarski(X0,X2)
% 1.99/0.90      | X0 != X3
% 1.99/0.90      | k3_subset_1(X1,X2) != k1_xboole_0 ),
% 1.99/0.90      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_237,plain,
% 1.99/0.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.90      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.99/0.90      | r1_tarski(X2,X0)
% 1.99/0.90      | k3_subset_1(X1,X0) != k1_xboole_0 ),
% 1.99/0.90      inference(unflattening,[status(thm)],[c_236]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_259,plain,
% 1.99/0.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.90      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.99/0.90      | X2 != X3
% 1.99/0.90      | X0 != X4
% 1.99/0.90      | k3_subset_1(X1,X0) != k1_xboole_0
% 1.99/0.90      | k3_xboole_0(X3,X4) = X3 ),
% 1.99/0.90      inference(resolution_lifted,[status(thm)],[c_6,c_237]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_260,plain,
% 1.99/0.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.90      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.99/0.90      | k3_subset_1(X1,X2) != k1_xboole_0
% 1.99/0.90      | k3_xboole_0(X0,X2) = X0 ),
% 1.99/0.90      inference(unflattening,[status(thm)],[c_259]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_700,plain,
% 1.99/0.90      ( k3_subset_1(X0,X1) != k1_xboole_0
% 1.99/0.90      | k3_xboole_0(X2,X1) = X2
% 1.99/0.90      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 1.99/0.90      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_1390,plain,
% 1.99/0.90      ( k3_xboole_0(X0,X1) = X0
% 1.99/0.90      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.99/0.90      | m1_subset_1(X1,k1_zfmisc_1(X1)) != iProver_top ),
% 1.99/0.90      inference(superposition,[status(thm)],[c_1271,c_700]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_14,plain,
% 1.99/0.90      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 1.99/0.90      inference(cnf_transformation,[],[f64]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_707,plain,
% 1.99/0.90      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_734,plain,
% 1.99/0.90      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.99/0.90      inference(light_normalisation,[status(thm)],[c_707,c_12]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_3145,plain,
% 1.99/0.90      ( k3_xboole_0(X0,X1) = X0
% 1.99/0.90      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 1.99/0.90      inference(forward_subsumption_resolution,
% 1.99/0.90                [status(thm)],
% 1.99/0.90                [c_1390,c_734]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_3149,plain,
% 1.99/0.90      ( k3_xboole_0(sK1,sK0) = sK1 ),
% 1.99/0.90      inference(superposition,[status(thm)],[c_701,c_3145]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_3380,plain,
% 1.99/0.90      ( k3_xboole_0(sK0,sK1) = sK1 ),
% 1.99/0.90      inference(superposition,[status(thm)],[c_0,c_3149]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_13,plain,
% 1.99/0.90      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.90      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 1.99/0.90      inference(cnf_transformation,[],[f63]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_708,plain,
% 1.99/0.90      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 1.99/0.90      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_1487,plain,
% 1.99/0.90      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
% 1.99/0.90      inference(superposition,[status(thm)],[c_701,c_708]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_3,plain,
% 1.99/0.90      ( ~ r2_hidden(X0,X1)
% 1.99/0.90      | r2_hidden(X0,X2)
% 1.99/0.90      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 1.99/0.90      inference(cnf_transformation,[],[f38]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_715,plain,
% 1.99/0.90      ( r2_hidden(X0,X1) != iProver_top
% 1.99/0.90      | r2_hidden(X0,X2) = iProver_top
% 1.99/0.90      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_1979,plain,
% 1.99/0.90      ( r2_hidden(X0,k3_subset_1(sK0,sK1)) = iProver_top
% 1.99/0.90      | r2_hidden(X0,k3_xboole_0(sK0,sK1)) = iProver_top
% 1.99/0.90      | r2_hidden(X0,sK0) != iProver_top ),
% 1.99/0.90      inference(superposition,[status(thm)],[c_1487,c_715]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_19,negated_conjecture,
% 1.99/0.90      ( ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
% 1.99/0.90      inference(cnf_transformation,[],[f60]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_704,plain,
% 1.99/0.90      ( r2_hidden(sK2,k3_subset_1(sK0,sK1)) != iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_2435,plain,
% 1.99/0.90      ( r2_hidden(sK2,k3_xboole_0(sK0,sK1)) = iProver_top
% 1.99/0.90      | r2_hidden(sK2,sK0) != iProver_top ),
% 1.99/0.90      inference(superposition,[status(thm)],[c_1979,c_704]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_23,negated_conjecture,
% 1.99/0.90      ( k1_xboole_0 != sK0 ),
% 1.99/0.90      inference(cnf_transformation,[],[f56]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_21,negated_conjecture,
% 1.99/0.90      ( m1_subset_1(sK2,sK0) ),
% 1.99/0.90      inference(cnf_transformation,[],[f58]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_25,plain,
% 1.99/0.90      ( m1_subset_1(sK2,sK0) = iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_1,plain,
% 1.99/0.90      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.99/0.90      inference(cnf_transformation,[],[f35]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_843,plain,
% 1.99/0.90      ( ~ v1_xboole_0(sK0) | k1_xboole_0 = sK0 ),
% 1.99/0.90      inference(instantiation,[status(thm)],[c_1]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_844,plain,
% 1.99/0.90      ( k1_xboole_0 = sK0 | v1_xboole_0(sK0) != iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_11,plain,
% 1.99/0.90      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.99/0.90      inference(cnf_transformation,[],[f43]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_859,plain,
% 1.99/0.90      ( ~ m1_subset_1(sK2,sK0) | r2_hidden(sK2,sK0) | v1_xboole_0(sK0) ),
% 1.99/0.90      inference(instantiation,[status(thm)],[c_11]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_860,plain,
% 1.99/0.90      ( m1_subset_1(sK2,sK0) != iProver_top
% 1.99/0.90      | r2_hidden(sK2,sK0) = iProver_top
% 1.99/0.90      | v1_xboole_0(sK0) = iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_2523,plain,
% 1.99/0.90      ( r2_hidden(sK2,k3_xboole_0(sK0,sK1)) = iProver_top ),
% 1.99/0.90      inference(global_propositional_subsumption,
% 1.99/0.90                [status(thm)],
% 1.99/0.90                [c_2435,c_23,c_25,c_844,c_860]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_3526,plain,
% 1.99/0.90      ( r2_hidden(sK2,sK1) = iProver_top ),
% 1.99/0.90      inference(demodulation,[status(thm)],[c_3380,c_2523]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_20,negated_conjecture,
% 1.99/0.90      ( ~ r2_hidden(sK2,sK1) ),
% 1.99/0.90      inference(cnf_transformation,[],[f59]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(c_26,plain,
% 1.99/0.90      ( r2_hidden(sK2,sK1) != iProver_top ),
% 1.99/0.90      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.99/0.90  
% 1.99/0.90  cnf(contradiction,plain,
% 1.99/0.90      ( $false ),
% 1.99/0.90      inference(minisat,[status(thm)],[c_3526,c_26]) ).
% 1.99/0.90  
% 1.99/0.90  
% 1.99/0.90  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/0.90  
% 1.99/0.90  ------                               Statistics
% 1.99/0.90  
% 1.99/0.90  ------ General
% 1.99/0.90  
% 1.99/0.90  abstr_ref_over_cycles:                  0
% 1.99/0.90  abstr_ref_under_cycles:                 0
% 1.99/0.90  gc_basic_clause_elim:                   0
% 1.99/0.90  forced_gc_time:                         0
% 1.99/0.90  parsing_time:                           0.006
% 1.99/0.90  unif_index_cands_time:                  0.
% 1.99/0.90  unif_index_add_time:                    0.
% 1.99/0.90  orderings_time:                         0.
% 1.99/0.90  out_proof_time:                         0.012
% 1.99/0.90  total_time:                             0.119
% 1.99/0.90  num_of_symbols:                         44
% 1.99/0.90  num_of_terms:                           2710
% 1.99/0.90  
% 1.99/0.90  ------ Preprocessing
% 1.99/0.90  
% 1.99/0.90  num_of_splits:                          0
% 1.99/0.90  num_of_split_atoms:                     0
% 1.99/0.90  num_of_reused_defs:                     0
% 1.99/0.90  num_eq_ax_congr_red:                    15
% 1.99/0.90  num_of_sem_filtered_clauses:            1
% 1.99/0.90  num_of_subtypes:                        0
% 1.99/0.90  monotx_restored_types:                  0
% 1.99/0.90  sat_num_of_epr_types:                   0
% 1.99/0.90  sat_num_of_non_cyclic_types:            0
% 1.99/0.90  sat_guarded_non_collapsed_types:        0
% 1.99/0.90  num_pure_diseq_elim:                    0
% 1.99/0.90  simp_replaced_by:                       0
% 1.99/0.90  res_preprocessed:                       102
% 1.99/0.90  prep_upred:                             0
% 1.99/0.90  prep_unflattend:                        3
% 1.99/0.90  smt_new_axioms:                         0
% 1.99/0.90  pred_elim_cands:                        3
% 1.99/0.90  pred_elim:                              2
% 1.99/0.90  pred_elim_cl:                           3
% 1.99/0.90  pred_elim_cycles:                       4
% 1.99/0.90  merged_defs:                            0
% 1.99/0.90  merged_defs_ncl:                        0
% 1.99/0.90  bin_hyper_res:                          0
% 1.99/0.90  prep_cycles:                            4
% 1.99/0.90  pred_elim_time:                         0.
% 1.99/0.90  splitting_time:                         0.
% 1.99/0.90  sem_filter_time:                        0.
% 1.99/0.90  monotx_time:                            0.
% 1.99/0.90  subtype_inf_time:                       0.
% 1.99/0.90  
% 1.99/0.90  ------ Problem properties
% 1.99/0.90  
% 1.99/0.90  clauses:                                21
% 1.99/0.90  conjectures:                            5
% 1.99/0.90  epr:                                    8
% 1.99/0.90  horn:                                   16
% 1.99/0.90  ground:                                 5
% 1.99/0.90  unary:                                  9
% 1.99/0.90  binary:                                 3
% 1.99/0.90  lits:                                   43
% 1.99/0.90  lits_eq:                                8
% 1.99/0.90  fd_pure:                                0
% 1.99/0.90  fd_pseudo:                              0
% 1.99/0.90  fd_cond:                                1
% 1.99/0.90  fd_pseudo_cond:                         0
% 1.99/0.90  ac_symbols:                             0
% 1.99/0.90  
% 1.99/0.90  ------ Propositional Solver
% 1.99/0.90  
% 1.99/0.90  prop_solver_calls:                      28
% 1.99/0.90  prop_fast_solver_calls:                 553
% 1.99/0.90  smt_solver_calls:                       0
% 1.99/0.90  smt_fast_solver_calls:                  0
% 1.99/0.90  prop_num_of_clauses:                    1310
% 1.99/0.90  prop_preprocess_simplified:             4096
% 1.99/0.90  prop_fo_subsumed:                       3
% 1.99/0.90  prop_solver_time:                       0.
% 1.99/0.90  smt_solver_time:                        0.
% 1.99/0.90  smt_fast_solver_time:                   0.
% 1.99/0.90  prop_fast_solver_time:                  0.
% 1.99/0.90  prop_unsat_core_time:                   0.
% 1.99/0.90  
% 1.99/0.90  ------ QBF
% 1.99/0.90  
% 1.99/0.90  qbf_q_res:                              0
% 1.99/0.90  qbf_num_tautologies:                    0
% 1.99/0.90  qbf_prep_cycles:                        0
% 1.99/0.90  
% 1.99/0.90  ------ BMC1
% 1.99/0.90  
% 1.99/0.90  bmc1_current_bound:                     -1
% 1.99/0.90  bmc1_last_solved_bound:                 -1
% 1.99/0.90  bmc1_unsat_core_size:                   -1
% 1.99/0.90  bmc1_unsat_core_parents_size:           -1
% 1.99/0.90  bmc1_merge_next_fun:                    0
% 1.99/0.90  bmc1_unsat_core_clauses_time:           0.
% 1.99/0.90  
% 1.99/0.90  ------ Instantiation
% 1.99/0.90  
% 1.99/0.90  inst_num_of_clauses:                    404
% 1.99/0.90  inst_num_in_passive:                    77
% 1.99/0.90  inst_num_in_active:                     207
% 1.99/0.90  inst_num_in_unprocessed:                120
% 1.99/0.90  inst_num_of_loops:                      260
% 1.99/0.90  inst_num_of_learning_restarts:          0
% 1.99/0.90  inst_num_moves_active_passive:          50
% 1.99/0.90  inst_lit_activity:                      0
% 1.99/0.90  inst_lit_activity_moves:                0
% 1.99/0.90  inst_num_tautologies:                   0
% 1.99/0.90  inst_num_prop_implied:                  0
% 1.99/0.90  inst_num_existing_simplified:           0
% 1.99/0.90  inst_num_eq_res_simplified:             0
% 1.99/0.90  inst_num_child_elim:                    0
% 1.99/0.90  inst_num_of_dismatching_blockings:      230
% 1.99/0.90  inst_num_of_non_proper_insts:           395
% 1.99/0.90  inst_num_of_duplicates:                 0
% 1.99/0.90  inst_inst_num_from_inst_to_res:         0
% 1.99/0.90  inst_dismatching_checking_time:         0.
% 1.99/0.90  
% 1.99/0.90  ------ Resolution
% 1.99/0.90  
% 1.99/0.90  res_num_of_clauses:                     0
% 1.99/0.90  res_num_in_passive:                     0
% 1.99/0.90  res_num_in_active:                      0
% 1.99/0.90  res_num_of_loops:                       106
% 1.99/0.90  res_forward_subset_subsumed:            42
% 1.99/0.90  res_backward_subset_subsumed:           0
% 1.99/0.90  res_forward_subsumed:                   0
% 1.99/0.90  res_backward_subsumed:                  0
% 1.99/0.90  res_forward_subsumption_resolution:     0
% 1.99/0.90  res_backward_subsumption_resolution:    0
% 1.99/0.90  res_clause_to_clause_subsumption:       128
% 1.99/0.90  res_orphan_elimination:                 0
% 1.99/0.90  res_tautology_del:                      30
% 1.99/0.90  res_num_eq_res_simplified:              0
% 1.99/0.90  res_num_sel_changes:                    0
% 1.99/0.90  res_moves_from_active_to_pass:          0
% 1.99/0.90  
% 1.99/0.90  ------ Superposition
% 1.99/0.90  
% 1.99/0.90  sup_time_total:                         0.
% 1.99/0.90  sup_time_generating:                    0.
% 1.99/0.90  sup_time_sim_full:                      0.
% 1.99/0.90  sup_time_sim_immed:                     0.
% 1.99/0.90  
% 1.99/0.90  sup_num_of_clauses:                     62
% 1.99/0.90  sup_num_in_active:                      38
% 1.99/0.90  sup_num_in_passive:                     24
% 1.99/0.90  sup_num_of_loops:                       50
% 1.99/0.90  sup_fw_superposition:                   51
% 1.99/0.90  sup_bw_superposition:                   37
% 1.99/0.90  sup_immediate_simplified:               12
% 1.99/0.90  sup_given_eliminated:                   0
% 1.99/0.90  comparisons_done:                       0
% 1.99/0.90  comparisons_avoided:                    0
% 1.99/0.90  
% 1.99/0.90  ------ Simplifications
% 1.99/0.90  
% 1.99/0.90  
% 1.99/0.90  sim_fw_subset_subsumed:                 5
% 1.99/0.90  sim_bw_subset_subsumed:                 0
% 1.99/0.90  sim_fw_subsumed:                        4
% 1.99/0.90  sim_bw_subsumed:                        0
% 1.99/0.90  sim_fw_subsumption_res:                 2
% 1.99/0.90  sim_bw_subsumption_res:                 0
% 1.99/0.90  sim_tautology_del:                      16
% 1.99/0.90  sim_eq_tautology_del:                   0
% 1.99/0.90  sim_eq_res_simp:                        0
% 1.99/0.90  sim_fw_demodulated:                     0
% 1.99/0.90  sim_bw_demodulated:                     13
% 1.99/0.90  sim_light_normalised:                   9
% 1.99/0.90  sim_joinable_taut:                      0
% 1.99/0.90  sim_joinable_simp:                      0
% 1.99/0.90  sim_ac_normalised:                      0
% 1.99/0.90  sim_smt_subsumption:                    0
% 1.99/0.90  
%------------------------------------------------------------------------------
