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
% DateTime   : Thu Dec  3 11:39:33 EST 2020

% Result     : Theorem 11.67s
% Output     : CNFRefutation 11.67s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 315 expanded)
%              Number of clauses        :   64 ( 115 expanded)
%              Number of leaves         :   17 (  67 expanded)
%              Depth                    :   21
%              Number of atoms          :  304 (1081 expanded)
%              Number of equality atoms :  104 ( 197 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK3) )
        & ( r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK3) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | ~ r1_tarski(sK2,X2) )
          & ( r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | r1_tarski(sK2,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f36,f35])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f63,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f39,f50,f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_481,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_482,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_21,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_484,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_31])).

cnf(c_1331,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1335,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2482,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1331,c_1335])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_463,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_464,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_466,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_31])).

cnf(c_1332,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_2481,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1332,c_1335])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1343,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2720,plain,
    ( k2_xboole_0(sK3,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2481,c_1343])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1340,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3469,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2720,c_1340])).

cnf(c_6664,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK3),sK1) = sK1
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3469,c_1343])).

cnf(c_18157,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2482,c_6664])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1344,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_18880,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18157,c_1344])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1339,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_21925,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK3,X0)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18880,c_1339])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3465,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1340])).

cnf(c_36614,plain,
    ( r1_tarski(k4_xboole_0(sK2,X0),sK3) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21925,c_3465])).

cnf(c_36639,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK3) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36614])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1333,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_499,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_500,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_1420,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_500])).

cnf(c_508,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_509,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_1421,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_509])).

cnf(c_1517,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1333,c_1420,c_1421])).

cnf(c_2704,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1339])).

cnf(c_4209,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2704,c_3465])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1341,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1334,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1514,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1334,c_1420,c_1421])).

cnf(c_3511,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_1514])).

cnf(c_4661,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4209,c_3511])).

cnf(c_4667,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_4661,c_1343])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3510,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_1339])).

cnf(c_24019,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3510])).

cnf(c_25512,plain,
    ( r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_24019])).

cnf(c_31981,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK3) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4667,c_25512])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_77,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_79,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36639,c_31981,c_3511,c_79])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:12:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.67/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.67/1.99  
% 11.67/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.67/1.99  
% 11.67/1.99  ------  iProver source info
% 11.67/1.99  
% 11.67/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.67/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.67/1.99  git: non_committed_changes: false
% 11.67/1.99  git: last_make_outside_of_git: false
% 11.67/1.99  
% 11.67/1.99  ------ 
% 11.67/1.99  
% 11.67/1.99  ------ Input Options
% 11.67/1.99  
% 11.67/1.99  --out_options                           all
% 11.67/1.99  --tptp_safe_out                         true
% 11.67/1.99  --problem_path                          ""
% 11.67/1.99  --include_path                          ""
% 11.67/1.99  --clausifier                            res/vclausify_rel
% 11.67/1.99  --clausifier_options                    ""
% 11.67/1.99  --stdin                                 false
% 11.67/1.99  --stats_out                             all
% 11.67/1.99  
% 11.67/1.99  ------ General Options
% 11.67/1.99  
% 11.67/1.99  --fof                                   false
% 11.67/1.99  --time_out_real                         305.
% 11.67/1.99  --time_out_virtual                      -1.
% 11.67/1.99  --symbol_type_check                     false
% 11.67/1.99  --clausify_out                          false
% 11.67/1.99  --sig_cnt_out                           false
% 11.67/1.99  --trig_cnt_out                          false
% 11.67/1.99  --trig_cnt_out_tolerance                1.
% 11.67/1.99  --trig_cnt_out_sk_spl                   false
% 11.67/1.99  --abstr_cl_out                          false
% 11.67/1.99  
% 11.67/1.99  ------ Global Options
% 11.67/1.99  
% 11.67/1.99  --schedule                              default
% 11.67/1.99  --add_important_lit                     false
% 11.67/1.99  --prop_solver_per_cl                    1000
% 11.67/1.99  --min_unsat_core                        false
% 11.67/1.99  --soft_assumptions                      false
% 11.67/1.99  --soft_lemma_size                       3
% 11.67/1.99  --prop_impl_unit_size                   0
% 11.67/1.99  --prop_impl_unit                        []
% 11.67/1.99  --share_sel_clauses                     true
% 11.67/1.99  --reset_solvers                         false
% 11.67/1.99  --bc_imp_inh                            [conj_cone]
% 11.67/1.99  --conj_cone_tolerance                   3.
% 11.67/1.99  --extra_neg_conj                        none
% 11.67/1.99  --large_theory_mode                     true
% 11.67/1.99  --prolific_symb_bound                   200
% 11.67/1.99  --lt_threshold                          2000
% 11.67/1.99  --clause_weak_htbl                      true
% 11.67/1.99  --gc_record_bc_elim                     false
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing Options
% 11.67/1.99  
% 11.67/1.99  --preprocessing_flag                    true
% 11.67/1.99  --time_out_prep_mult                    0.1
% 11.67/1.99  --splitting_mode                        input
% 11.67/1.99  --splitting_grd                         true
% 11.67/1.99  --splitting_cvd                         false
% 11.67/1.99  --splitting_cvd_svl                     false
% 11.67/1.99  --splitting_nvd                         32
% 11.67/1.99  --sub_typing                            true
% 11.67/1.99  --prep_gs_sim                           true
% 11.67/1.99  --prep_unflatten                        true
% 11.67/1.99  --prep_res_sim                          true
% 11.67/1.99  --prep_upred                            true
% 11.67/1.99  --prep_sem_filter                       exhaustive
% 11.67/1.99  --prep_sem_filter_out                   false
% 11.67/1.99  --pred_elim                             true
% 11.67/1.99  --res_sim_input                         true
% 11.67/1.99  --eq_ax_congr_red                       true
% 11.67/1.99  --pure_diseq_elim                       true
% 11.67/1.99  --brand_transform                       false
% 11.67/1.99  --non_eq_to_eq                          false
% 11.67/1.99  --prep_def_merge                        true
% 11.67/1.99  --prep_def_merge_prop_impl              false
% 11.67/1.99  --prep_def_merge_mbd                    true
% 11.67/1.99  --prep_def_merge_tr_red                 false
% 11.67/1.99  --prep_def_merge_tr_cl                  false
% 11.67/1.99  --smt_preprocessing                     true
% 11.67/1.99  --smt_ac_axioms                         fast
% 11.67/1.99  --preprocessed_out                      false
% 11.67/1.99  --preprocessed_stats                    false
% 11.67/1.99  
% 11.67/1.99  ------ Abstraction refinement Options
% 11.67/1.99  
% 11.67/1.99  --abstr_ref                             []
% 11.67/1.99  --abstr_ref_prep                        false
% 11.67/1.99  --abstr_ref_until_sat                   false
% 11.67/1.99  --abstr_ref_sig_restrict                funpre
% 11.67/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.67/1.99  --abstr_ref_under                       []
% 11.67/1.99  
% 11.67/1.99  ------ SAT Options
% 11.67/1.99  
% 11.67/1.99  --sat_mode                              false
% 11.67/1.99  --sat_fm_restart_options                ""
% 11.67/1.99  --sat_gr_def                            false
% 11.67/1.99  --sat_epr_types                         true
% 11.67/1.99  --sat_non_cyclic_types                  false
% 11.67/1.99  --sat_finite_models                     false
% 11.67/1.99  --sat_fm_lemmas                         false
% 11.67/1.99  --sat_fm_prep                           false
% 11.67/1.99  --sat_fm_uc_incr                        true
% 11.67/1.99  --sat_out_model                         small
% 11.67/1.99  --sat_out_clauses                       false
% 11.67/1.99  
% 11.67/1.99  ------ QBF Options
% 11.67/1.99  
% 11.67/1.99  --qbf_mode                              false
% 11.67/1.99  --qbf_elim_univ                         false
% 11.67/1.99  --qbf_dom_inst                          none
% 11.67/1.99  --qbf_dom_pre_inst                      false
% 11.67/1.99  --qbf_sk_in                             false
% 11.67/1.99  --qbf_pred_elim                         true
% 11.67/1.99  --qbf_split                             512
% 11.67/1.99  
% 11.67/1.99  ------ BMC1 Options
% 11.67/1.99  
% 11.67/1.99  --bmc1_incremental                      false
% 11.67/1.99  --bmc1_axioms                           reachable_all
% 11.67/1.99  --bmc1_min_bound                        0
% 11.67/1.99  --bmc1_max_bound                        -1
% 11.67/1.99  --bmc1_max_bound_default                -1
% 11.67/1.99  --bmc1_symbol_reachability              true
% 11.67/1.99  --bmc1_property_lemmas                  false
% 11.67/1.99  --bmc1_k_induction                      false
% 11.67/1.99  --bmc1_non_equiv_states                 false
% 11.67/1.99  --bmc1_deadlock                         false
% 11.67/1.99  --bmc1_ucm                              false
% 11.67/1.99  --bmc1_add_unsat_core                   none
% 11.67/1.99  --bmc1_unsat_core_children              false
% 11.67/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.67/1.99  --bmc1_out_stat                         full
% 11.67/1.99  --bmc1_ground_init                      false
% 11.67/1.99  --bmc1_pre_inst_next_state              false
% 11.67/1.99  --bmc1_pre_inst_state                   false
% 11.67/1.99  --bmc1_pre_inst_reach_state             false
% 11.67/1.99  --bmc1_out_unsat_core                   false
% 11.67/1.99  --bmc1_aig_witness_out                  false
% 11.67/1.99  --bmc1_verbose                          false
% 11.67/1.99  --bmc1_dump_clauses_tptp                false
% 11.67/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.67/1.99  --bmc1_dump_file                        -
% 11.67/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.67/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.67/1.99  --bmc1_ucm_extend_mode                  1
% 11.67/1.99  --bmc1_ucm_init_mode                    2
% 11.67/1.99  --bmc1_ucm_cone_mode                    none
% 11.67/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.67/1.99  --bmc1_ucm_relax_model                  4
% 11.67/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.67/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.67/1.99  --bmc1_ucm_layered_model                none
% 11.67/1.99  --bmc1_ucm_max_lemma_size               10
% 11.67/1.99  
% 11.67/1.99  ------ AIG Options
% 11.67/1.99  
% 11.67/1.99  --aig_mode                              false
% 11.67/1.99  
% 11.67/1.99  ------ Instantiation Options
% 11.67/1.99  
% 11.67/1.99  --instantiation_flag                    true
% 11.67/1.99  --inst_sos_flag                         true
% 11.67/1.99  --inst_sos_phase                        true
% 11.67/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.67/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.67/1.99  --inst_lit_sel_side                     num_symb
% 11.67/1.99  --inst_solver_per_active                1400
% 11.67/1.99  --inst_solver_calls_frac                1.
% 11.67/1.99  --inst_passive_queue_type               priority_queues
% 11.67/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.67/1.99  --inst_passive_queues_freq              [25;2]
% 11.67/1.99  --inst_dismatching                      true
% 11.67/1.99  --inst_eager_unprocessed_to_passive     true
% 11.67/1.99  --inst_prop_sim_given                   true
% 11.67/1.99  --inst_prop_sim_new                     false
% 11.67/1.99  --inst_subs_new                         false
% 11.67/1.99  --inst_eq_res_simp                      false
% 11.67/1.99  --inst_subs_given                       false
% 11.67/1.99  --inst_orphan_elimination               true
% 11.67/1.99  --inst_learning_loop_flag               true
% 11.67/1.99  --inst_learning_start                   3000
% 11.67/1.99  --inst_learning_factor                  2
% 11.67/1.99  --inst_start_prop_sim_after_learn       3
% 11.67/1.99  --inst_sel_renew                        solver
% 11.67/1.99  --inst_lit_activity_flag                true
% 11.67/1.99  --inst_restr_to_given                   false
% 11.67/1.99  --inst_activity_threshold               500
% 11.67/1.99  --inst_out_proof                        true
% 11.67/1.99  
% 11.67/1.99  ------ Resolution Options
% 11.67/1.99  
% 11.67/1.99  --resolution_flag                       true
% 11.67/1.99  --res_lit_sel                           adaptive
% 11.67/1.99  --res_lit_sel_side                      none
% 11.67/1.99  --res_ordering                          kbo
% 11.67/1.99  --res_to_prop_solver                    active
% 11.67/1.99  --res_prop_simpl_new                    false
% 11.67/1.99  --res_prop_simpl_given                  true
% 11.67/1.99  --res_passive_queue_type                priority_queues
% 11.67/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.67/1.99  --res_passive_queues_freq               [15;5]
% 11.67/1.99  --res_forward_subs                      full
% 11.67/1.99  --res_backward_subs                     full
% 11.67/1.99  --res_forward_subs_resolution           true
% 11.67/1.99  --res_backward_subs_resolution          true
% 11.67/1.99  --res_orphan_elimination                true
% 11.67/1.99  --res_time_limit                        2.
% 11.67/1.99  --res_out_proof                         true
% 11.67/1.99  
% 11.67/1.99  ------ Superposition Options
% 11.67/1.99  
% 11.67/1.99  --superposition_flag                    true
% 11.67/1.99  --sup_passive_queue_type                priority_queues
% 11.67/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.67/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.67/1.99  --demod_completeness_check              fast
% 11.67/1.99  --demod_use_ground                      true
% 11.67/1.99  --sup_to_prop_solver                    passive
% 11.67/1.99  --sup_prop_simpl_new                    true
% 11.67/1.99  --sup_prop_simpl_given                  true
% 11.67/1.99  --sup_fun_splitting                     true
% 11.67/1.99  --sup_smt_interval                      50000
% 11.67/1.99  
% 11.67/1.99  ------ Superposition Simplification Setup
% 11.67/1.99  
% 11.67/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.67/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.67/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.67/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.67/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.67/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.67/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.67/1.99  --sup_immed_triv                        [TrivRules]
% 11.67/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_immed_bw_main                     []
% 11.67/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.67/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.67/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_input_bw                          []
% 11.67/1.99  
% 11.67/1.99  ------ Combination Options
% 11.67/1.99  
% 11.67/1.99  --comb_res_mult                         3
% 11.67/1.99  --comb_sup_mult                         2
% 11.67/1.99  --comb_inst_mult                        10
% 11.67/1.99  
% 11.67/1.99  ------ Debug Options
% 11.67/1.99  
% 11.67/1.99  --dbg_backtrace                         false
% 11.67/1.99  --dbg_dump_prop_clauses                 false
% 11.67/1.99  --dbg_dump_prop_clauses_file            -
% 11.67/1.99  --dbg_out_stat                          false
% 11.67/1.99  ------ Parsing...
% 11.67/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.67/1.99  ------ Proving...
% 11.67/1.99  ------ Problem Properties 
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  clauses                                 22
% 11.67/1.99  conjectures                             2
% 11.67/1.99  EPR                                     3
% 11.67/1.99  Horn                                    20
% 11.67/1.99  unary                                   7
% 11.67/1.99  binary                                  12
% 11.67/1.99  lits                                    40
% 11.67/1.99  lits eq                                 12
% 11.67/1.99  fd_pure                                 0
% 11.67/1.99  fd_pseudo                               0
% 11.67/1.99  fd_cond                                 0
% 11.67/1.99  fd_pseudo_cond                          3
% 11.67/1.99  AC symbols                              0
% 11.67/1.99  
% 11.67/1.99  ------ Schedule dynamic 5 is on 
% 11.67/1.99  
% 11.67/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  ------ 
% 11.67/1.99  Current options:
% 11.67/1.99  ------ 
% 11.67/1.99  
% 11.67/1.99  ------ Input Options
% 11.67/1.99  
% 11.67/1.99  --out_options                           all
% 11.67/1.99  --tptp_safe_out                         true
% 11.67/1.99  --problem_path                          ""
% 11.67/1.99  --include_path                          ""
% 11.67/1.99  --clausifier                            res/vclausify_rel
% 11.67/1.99  --clausifier_options                    ""
% 11.67/1.99  --stdin                                 false
% 11.67/1.99  --stats_out                             all
% 11.67/1.99  
% 11.67/1.99  ------ General Options
% 11.67/1.99  
% 11.67/1.99  --fof                                   false
% 11.67/1.99  --time_out_real                         305.
% 11.67/1.99  --time_out_virtual                      -1.
% 11.67/1.99  --symbol_type_check                     false
% 11.67/1.99  --clausify_out                          false
% 11.67/1.99  --sig_cnt_out                           false
% 11.67/1.99  --trig_cnt_out                          false
% 11.67/1.99  --trig_cnt_out_tolerance                1.
% 11.67/1.99  --trig_cnt_out_sk_spl                   false
% 11.67/1.99  --abstr_cl_out                          false
% 11.67/1.99  
% 11.67/1.99  ------ Global Options
% 11.67/1.99  
% 11.67/1.99  --schedule                              default
% 11.67/1.99  --add_important_lit                     false
% 11.67/1.99  --prop_solver_per_cl                    1000
% 11.67/1.99  --min_unsat_core                        false
% 11.67/1.99  --soft_assumptions                      false
% 11.67/1.99  --soft_lemma_size                       3
% 11.67/1.99  --prop_impl_unit_size                   0
% 11.67/1.99  --prop_impl_unit                        []
% 11.67/1.99  --share_sel_clauses                     true
% 11.67/1.99  --reset_solvers                         false
% 11.67/1.99  --bc_imp_inh                            [conj_cone]
% 11.67/1.99  --conj_cone_tolerance                   3.
% 11.67/1.99  --extra_neg_conj                        none
% 11.67/1.99  --large_theory_mode                     true
% 11.67/1.99  --prolific_symb_bound                   200
% 11.67/1.99  --lt_threshold                          2000
% 11.67/1.99  --clause_weak_htbl                      true
% 11.67/1.99  --gc_record_bc_elim                     false
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing Options
% 11.67/1.99  
% 11.67/1.99  --preprocessing_flag                    true
% 11.67/1.99  --time_out_prep_mult                    0.1
% 11.67/1.99  --splitting_mode                        input
% 11.67/1.99  --splitting_grd                         true
% 11.67/1.99  --splitting_cvd                         false
% 11.67/1.99  --splitting_cvd_svl                     false
% 11.67/1.99  --splitting_nvd                         32
% 11.67/1.99  --sub_typing                            true
% 11.67/1.99  --prep_gs_sim                           true
% 11.67/1.99  --prep_unflatten                        true
% 11.67/1.99  --prep_res_sim                          true
% 11.67/1.99  --prep_upred                            true
% 11.67/1.99  --prep_sem_filter                       exhaustive
% 11.67/1.99  --prep_sem_filter_out                   false
% 11.67/1.99  --pred_elim                             true
% 11.67/1.99  --res_sim_input                         true
% 11.67/1.99  --eq_ax_congr_red                       true
% 11.67/1.99  --pure_diseq_elim                       true
% 11.67/1.99  --brand_transform                       false
% 11.67/1.99  --non_eq_to_eq                          false
% 11.67/1.99  --prep_def_merge                        true
% 11.67/1.99  --prep_def_merge_prop_impl              false
% 11.67/1.99  --prep_def_merge_mbd                    true
% 11.67/1.99  --prep_def_merge_tr_red                 false
% 11.67/1.99  --prep_def_merge_tr_cl                  false
% 11.67/1.99  --smt_preprocessing                     true
% 11.67/1.99  --smt_ac_axioms                         fast
% 11.67/1.99  --preprocessed_out                      false
% 11.67/1.99  --preprocessed_stats                    false
% 11.67/1.99  
% 11.67/1.99  ------ Abstraction refinement Options
% 11.67/1.99  
% 11.67/1.99  --abstr_ref                             []
% 11.67/1.99  --abstr_ref_prep                        false
% 11.67/1.99  --abstr_ref_until_sat                   false
% 11.67/1.99  --abstr_ref_sig_restrict                funpre
% 11.67/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.67/1.99  --abstr_ref_under                       []
% 11.67/1.99  
% 11.67/1.99  ------ SAT Options
% 11.67/1.99  
% 11.67/1.99  --sat_mode                              false
% 11.67/1.99  --sat_fm_restart_options                ""
% 11.67/1.99  --sat_gr_def                            false
% 11.67/1.99  --sat_epr_types                         true
% 11.67/1.99  --sat_non_cyclic_types                  false
% 11.67/1.99  --sat_finite_models                     false
% 11.67/1.99  --sat_fm_lemmas                         false
% 11.67/1.99  --sat_fm_prep                           false
% 11.67/1.99  --sat_fm_uc_incr                        true
% 11.67/1.99  --sat_out_model                         small
% 11.67/1.99  --sat_out_clauses                       false
% 11.67/1.99  
% 11.67/1.99  ------ QBF Options
% 11.67/1.99  
% 11.67/1.99  --qbf_mode                              false
% 11.67/1.99  --qbf_elim_univ                         false
% 11.67/1.99  --qbf_dom_inst                          none
% 11.67/1.99  --qbf_dom_pre_inst                      false
% 11.67/1.99  --qbf_sk_in                             false
% 11.67/1.99  --qbf_pred_elim                         true
% 11.67/1.99  --qbf_split                             512
% 11.67/1.99  
% 11.67/1.99  ------ BMC1 Options
% 11.67/1.99  
% 11.67/1.99  --bmc1_incremental                      false
% 11.67/1.99  --bmc1_axioms                           reachable_all
% 11.67/1.99  --bmc1_min_bound                        0
% 11.67/1.99  --bmc1_max_bound                        -1
% 11.67/1.99  --bmc1_max_bound_default                -1
% 11.67/1.99  --bmc1_symbol_reachability              true
% 11.67/1.99  --bmc1_property_lemmas                  false
% 11.67/1.99  --bmc1_k_induction                      false
% 11.67/1.99  --bmc1_non_equiv_states                 false
% 11.67/1.99  --bmc1_deadlock                         false
% 11.67/1.99  --bmc1_ucm                              false
% 11.67/1.99  --bmc1_add_unsat_core                   none
% 11.67/1.99  --bmc1_unsat_core_children              false
% 11.67/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.67/1.99  --bmc1_out_stat                         full
% 11.67/1.99  --bmc1_ground_init                      false
% 11.67/1.99  --bmc1_pre_inst_next_state              false
% 11.67/1.99  --bmc1_pre_inst_state                   false
% 11.67/1.99  --bmc1_pre_inst_reach_state             false
% 11.67/1.99  --bmc1_out_unsat_core                   false
% 11.67/1.99  --bmc1_aig_witness_out                  false
% 11.67/1.99  --bmc1_verbose                          false
% 11.67/1.99  --bmc1_dump_clauses_tptp                false
% 11.67/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.67/1.99  --bmc1_dump_file                        -
% 11.67/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.67/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.67/1.99  --bmc1_ucm_extend_mode                  1
% 11.67/1.99  --bmc1_ucm_init_mode                    2
% 11.67/1.99  --bmc1_ucm_cone_mode                    none
% 11.67/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.67/1.99  --bmc1_ucm_relax_model                  4
% 11.67/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.67/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.67/1.99  --bmc1_ucm_layered_model                none
% 11.67/1.99  --bmc1_ucm_max_lemma_size               10
% 11.67/1.99  
% 11.67/1.99  ------ AIG Options
% 11.67/1.99  
% 11.67/1.99  --aig_mode                              false
% 11.67/1.99  
% 11.67/1.99  ------ Instantiation Options
% 11.67/1.99  
% 11.67/1.99  --instantiation_flag                    true
% 11.67/1.99  --inst_sos_flag                         true
% 11.67/1.99  --inst_sos_phase                        true
% 11.67/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.67/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.67/1.99  --inst_lit_sel_side                     none
% 11.67/1.99  --inst_solver_per_active                1400
% 11.67/1.99  --inst_solver_calls_frac                1.
% 11.67/1.99  --inst_passive_queue_type               priority_queues
% 11.67/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.67/1.99  --inst_passive_queues_freq              [25;2]
% 11.67/1.99  --inst_dismatching                      true
% 11.67/1.99  --inst_eager_unprocessed_to_passive     true
% 11.67/1.99  --inst_prop_sim_given                   true
% 11.67/1.99  --inst_prop_sim_new                     false
% 11.67/1.99  --inst_subs_new                         false
% 11.67/1.99  --inst_eq_res_simp                      false
% 11.67/1.99  --inst_subs_given                       false
% 11.67/1.99  --inst_orphan_elimination               true
% 11.67/1.99  --inst_learning_loop_flag               true
% 11.67/1.99  --inst_learning_start                   3000
% 11.67/1.99  --inst_learning_factor                  2
% 11.67/1.99  --inst_start_prop_sim_after_learn       3
% 11.67/1.99  --inst_sel_renew                        solver
% 11.67/1.99  --inst_lit_activity_flag                true
% 11.67/1.99  --inst_restr_to_given                   false
% 11.67/1.99  --inst_activity_threshold               500
% 11.67/1.99  --inst_out_proof                        true
% 11.67/1.99  
% 11.67/1.99  ------ Resolution Options
% 11.67/1.99  
% 11.67/1.99  --resolution_flag                       false
% 11.67/1.99  --res_lit_sel                           adaptive
% 11.67/1.99  --res_lit_sel_side                      none
% 11.67/1.99  --res_ordering                          kbo
% 11.67/1.99  --res_to_prop_solver                    active
% 11.67/1.99  --res_prop_simpl_new                    false
% 11.67/1.99  --res_prop_simpl_given                  true
% 11.67/1.99  --res_passive_queue_type                priority_queues
% 11.67/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.67/1.99  --res_passive_queues_freq               [15;5]
% 11.67/1.99  --res_forward_subs                      full
% 11.67/1.99  --res_backward_subs                     full
% 11.67/1.99  --res_forward_subs_resolution           true
% 11.67/1.99  --res_backward_subs_resolution          true
% 11.67/1.99  --res_orphan_elimination                true
% 11.67/1.99  --res_time_limit                        2.
% 11.67/1.99  --res_out_proof                         true
% 11.67/1.99  
% 11.67/1.99  ------ Superposition Options
% 11.67/1.99  
% 11.67/1.99  --superposition_flag                    true
% 11.67/1.99  --sup_passive_queue_type                priority_queues
% 11.67/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.67/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.67/1.99  --demod_completeness_check              fast
% 11.67/1.99  --demod_use_ground                      true
% 11.67/1.99  --sup_to_prop_solver                    passive
% 11.67/1.99  --sup_prop_simpl_new                    true
% 11.67/1.99  --sup_prop_simpl_given                  true
% 11.67/1.99  --sup_fun_splitting                     true
% 11.67/1.99  --sup_smt_interval                      50000
% 11.67/1.99  
% 11.67/1.99  ------ Superposition Simplification Setup
% 11.67/1.99  
% 11.67/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.67/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.67/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.67/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.67/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.67/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.67/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.67/1.99  --sup_immed_triv                        [TrivRules]
% 11.67/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_immed_bw_main                     []
% 11.67/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.67/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.67/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_input_bw                          []
% 11.67/1.99  
% 11.67/1.99  ------ Combination Options
% 11.67/1.99  
% 11.67/1.99  --comb_res_mult                         3
% 11.67/1.99  --comb_sup_mult                         2
% 11.67/1.99  --comb_inst_mult                        10
% 11.67/1.99  
% 11.67/1.99  ------ Debug Options
% 11.67/1.99  
% 11.67/1.99  --dbg_backtrace                         false
% 11.67/1.99  --dbg_dump_prop_clauses                 false
% 11.67/1.99  --dbg_dump_prop_clauses_file            -
% 11.67/1.99  --dbg_out_stat                          false
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  ------ Proving...
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  % SZS status Theorem for theBenchmark.p
% 11.67/1.99  
% 11.67/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.67/1.99  
% 11.67/1.99  fof(f13,axiom,(
% 11.67/1.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f23,plain,(
% 11.67/1.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.67/1.99    inference(ennf_transformation,[],[f13])).
% 11.67/1.99  
% 11.67/1.99  fof(f32,plain,(
% 11.67/1.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.67/1.99    inference(nnf_transformation,[],[f23])).
% 11.67/1.99  
% 11.67/1.99  fof(f55,plain,(
% 11.67/1.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f32])).
% 11.67/1.99  
% 11.67/1.99  fof(f16,conjecture,(
% 11.67/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f17,negated_conjecture,(
% 11.67/1.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 11.67/1.99    inference(negated_conjecture,[],[f16])).
% 11.67/1.99  
% 11.67/1.99  fof(f25,plain,(
% 11.67/1.99    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.67/1.99    inference(ennf_transformation,[],[f17])).
% 11.67/1.99  
% 11.67/1.99  fof(f33,plain,(
% 11.67/1.99    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.67/1.99    inference(nnf_transformation,[],[f25])).
% 11.67/1.99  
% 11.67/1.99  fof(f34,plain,(
% 11.67/1.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.67/1.99    inference(flattening,[],[f33])).
% 11.67/1.99  
% 11.67/1.99  fof(f36,plain,(
% 11.67/1.99    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 11.67/1.99    introduced(choice_axiom,[])).
% 11.67/1.99  
% 11.67/1.99  fof(f35,plain,(
% 11.67/1.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 11.67/1.99    introduced(choice_axiom,[])).
% 11.67/1.99  
% 11.67/1.99  fof(f37,plain,(
% 11.67/1.99    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.67/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f36,f35])).
% 11.67/1.99  
% 11.67/1.99  fof(f61,plain,(
% 11.67/1.99    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.67/1.99    inference(cnf_transformation,[],[f37])).
% 11.67/1.99  
% 11.67/1.99  fof(f15,axiom,(
% 11.67/1.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f60,plain,(
% 11.67/1.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.67/1.99    inference(cnf_transformation,[],[f15])).
% 11.67/1.99  
% 11.67/1.99  fof(f12,axiom,(
% 11.67/1.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f28,plain,(
% 11.67/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.67/1.99    inference(nnf_transformation,[],[f12])).
% 11.67/1.99  
% 11.67/1.99  fof(f29,plain,(
% 11.67/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.67/1.99    inference(rectify,[],[f28])).
% 11.67/1.99  
% 11.67/1.99  fof(f30,plain,(
% 11.67/1.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 11.67/1.99    introduced(choice_axiom,[])).
% 11.67/1.99  
% 11.67/1.99  fof(f31,plain,(
% 11.67/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.67/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 11.67/1.99  
% 11.67/1.99  fof(f51,plain,(
% 11.67/1.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.67/1.99    inference(cnf_transformation,[],[f31])).
% 11.67/1.99  
% 11.67/1.99  fof(f69,plain,(
% 11.67/1.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.67/1.99    inference(equality_resolution,[],[f51])).
% 11.67/1.99  
% 11.67/1.99  fof(f62,plain,(
% 11.67/1.99    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 11.67/1.99    inference(cnf_transformation,[],[f37])).
% 11.67/1.99  
% 11.67/1.99  fof(f5,axiom,(
% 11.67/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f19,plain,(
% 11.67/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.67/1.99    inference(ennf_transformation,[],[f5])).
% 11.67/1.99  
% 11.67/1.99  fof(f44,plain,(
% 11.67/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f19])).
% 11.67/1.99  
% 11.67/1.99  fof(f9,axiom,(
% 11.67/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f21,plain,(
% 11.67/1.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.67/1.99    inference(ennf_transformation,[],[f9])).
% 11.67/1.99  
% 11.67/1.99  fof(f48,plain,(
% 11.67/1.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.67/1.99    inference(cnf_transformation,[],[f21])).
% 11.67/1.99  
% 11.67/1.99  fof(f4,axiom,(
% 11.67/1.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f18,plain,(
% 11.67/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.67/1.99    inference(ennf_transformation,[],[f4])).
% 11.67/1.99  
% 11.67/1.99  fof(f43,plain,(
% 11.67/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f18])).
% 11.67/1.99  
% 11.67/1.99  fof(f10,axiom,(
% 11.67/1.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f22,plain,(
% 11.67/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.67/1.99    inference(ennf_transformation,[],[f10])).
% 11.67/1.99  
% 11.67/1.99  fof(f49,plain,(
% 11.67/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f22])).
% 11.67/1.99  
% 11.67/1.99  fof(f1,axiom,(
% 11.67/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f38,plain,(
% 11.67/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f1])).
% 11.67/1.99  
% 11.67/1.99  fof(f63,plain,(
% 11.67/1.99    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 11.67/1.99    inference(cnf_transformation,[],[f37])).
% 11.67/1.99  
% 11.67/1.99  fof(f14,axiom,(
% 11.67/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f24,plain,(
% 11.67/1.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.67/1.99    inference(ennf_transformation,[],[f14])).
% 11.67/1.99  
% 11.67/1.99  fof(f59,plain,(
% 11.67/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.67/1.99    inference(cnf_transformation,[],[f24])).
% 11.67/1.99  
% 11.67/1.99  fof(f7,axiom,(
% 11.67/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f20,plain,(
% 11.67/1.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 11.67/1.99    inference(ennf_transformation,[],[f7])).
% 11.67/1.99  
% 11.67/1.99  fof(f46,plain,(
% 11.67/1.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f20])).
% 11.67/1.99  
% 11.67/1.99  fof(f64,plain,(
% 11.67/1.99    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 11.67/1.99    inference(cnf_transformation,[],[f37])).
% 11.67/1.99  
% 11.67/1.99  fof(f2,axiom,(
% 11.67/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f39,plain,(
% 11.67/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f2])).
% 11.67/1.99  
% 11.67/1.99  fof(f11,axiom,(
% 11.67/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f50,plain,(
% 11.67/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.67/1.99    inference(cnf_transformation,[],[f11])).
% 11.67/1.99  
% 11.67/1.99  fof(f65,plain,(
% 11.67/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.67/1.99    inference(definition_unfolding,[],[f39,f50,f50])).
% 11.67/1.99  
% 11.67/1.99  fof(f3,axiom,(
% 11.67/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.67/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f26,plain,(
% 11.67/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.67/1.99    inference(nnf_transformation,[],[f3])).
% 11.67/1.99  
% 11.67/1.99  fof(f27,plain,(
% 11.67/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.67/1.99    inference(flattening,[],[f26])).
% 11.67/1.99  
% 11.67/1.99  fof(f40,plain,(
% 11.67/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.67/1.99    inference(cnf_transformation,[],[f27])).
% 11.67/1.99  
% 11.67/1.99  fof(f67,plain,(
% 11.67/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.67/1.99    inference(equality_resolution,[],[f40])).
% 11.67/1.99  
% 11.67/1.99  cnf(c_19,plain,
% 11.67/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.67/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_25,negated_conjecture,
% 11.67/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 11.67/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_481,plain,
% 11.67/1.99      ( r2_hidden(X0,X1)
% 11.67/1.99      | v1_xboole_0(X1)
% 11.67/1.99      | k1_zfmisc_1(sK1) != X1
% 11.67/1.99      | sK2 != X0 ),
% 11.67/1.99      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_482,plain,
% 11.67/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.67/1.99      inference(unflattening,[status(thm)],[c_481]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_21,plain,
% 11.67/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.67/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_31,plain,
% 11.67/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_21]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_484,plain,
% 11.67/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 11.67/1.99      inference(global_propositional_subsumption,
% 11.67/1.99                [status(thm)],
% 11.67/1.99                [c_482,c_31]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1331,plain,
% 11.67/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_15,plain,
% 11.67/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.67/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1335,plain,
% 11.67/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.67/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_2482,plain,
% 11.67/1.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_1331,c_1335]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_24,negated_conjecture,
% 11.67/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 11.67/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_463,plain,
% 11.67/1.99      ( r2_hidden(X0,X1)
% 11.67/1.99      | v1_xboole_0(X1)
% 11.67/1.99      | k1_zfmisc_1(sK1) != X1
% 11.67/1.99      | sK3 != X0 ),
% 11.67/1.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_464,plain,
% 11.67/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.67/1.99      inference(unflattening,[status(thm)],[c_463]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_466,plain,
% 11.67/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 11.67/1.99      inference(global_propositional_subsumption,
% 11.67/1.99                [status(thm)],
% 11.67/1.99                [c_464,c_31]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1332,plain,
% 11.67/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_2481,plain,
% 11.67/1.99      ( r1_tarski(sK3,sK1) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_1332,c_1335]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_6,plain,
% 11.67/1.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.67/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1343,plain,
% 11.67/1.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_2720,plain,
% 11.67/1.99      ( k2_xboole_0(sK3,sK1) = sK1 ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_2481,c_1343]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_10,plain,
% 11.67/1.99      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 11.67/1.99      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 11.67/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1340,plain,
% 11.67/1.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.67/1.99      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_3469,plain,
% 11.67/1.99      ( r1_tarski(X0,sK1) != iProver_top
% 11.67/1.99      | r1_tarski(k4_xboole_0(X0,sK3),sK1) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_2720,c_1340]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_6664,plain,
% 11.67/1.99      ( k2_xboole_0(k4_xboole_0(X0,sK3),sK1) = sK1
% 11.67/1.99      | r1_tarski(X0,sK1) != iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_3469,c_1343]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_18157,plain,
% 11.67/1.99      ( k2_xboole_0(k4_xboole_0(sK2,sK3),sK1) = sK1 ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_2482,c_6664]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_5,plain,
% 11.67/1.99      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 11.67/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1344,plain,
% 11.67/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.67/1.99      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_18880,plain,
% 11.67/1.99      ( r1_tarski(k4_xboole_0(sK2,sK3),X0) = iProver_top
% 11.67/1.99      | r1_tarski(sK1,X0) != iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_18157,c_1344]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_11,plain,
% 11.67/1.99      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 11.67/1.99      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 11.67/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1339,plain,
% 11.67/1.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 11.67/1.99      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_21925,plain,
% 11.67/1.99      ( r1_tarski(sK2,k2_xboole_0(sK3,X0)) = iProver_top
% 11.67/1.99      | r1_tarski(sK1,X0) != iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_18880,c_1339]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_0,plain,
% 11.67/1.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.67/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_3465,plain,
% 11.67/1.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.67/1.99      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_0,c_1340]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_36614,plain,
% 11.67/1.99      ( r1_tarski(k4_xboole_0(sK2,X0),sK3) = iProver_top
% 11.67/1.99      | r1_tarski(sK1,X0) != iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_21925,c_3465]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_36639,plain,
% 11.67/1.99      ( r1_tarski(k4_xboole_0(sK2,sK1),sK3) = iProver_top
% 11.67/1.99      | r1_tarski(sK1,sK1) != iProver_top ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_36614]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_23,negated_conjecture,
% 11.67/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 11.67/1.99      | r1_tarski(sK2,sK3) ),
% 11.67/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1333,plain,
% 11.67/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 11.67/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_20,plain,
% 11.67/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.67/1.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.67/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_499,plain,
% 11.67/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.67/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.67/1.99      | sK3 != X1 ),
% 11.67/1.99      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_500,plain,
% 11.67/1.99      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 11.67/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.67/1.99      inference(unflattening,[status(thm)],[c_499]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1420,plain,
% 11.67/1.99      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 11.67/1.99      inference(equality_resolution,[status(thm)],[c_500]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_508,plain,
% 11.67/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.67/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.67/1.99      | sK2 != X1 ),
% 11.67/1.99      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_509,plain,
% 11.67/1.99      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 11.67/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.67/1.99      inference(unflattening,[status(thm)],[c_508]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1421,plain,
% 11.67/1.99      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 11.67/1.99      inference(equality_resolution,[status(thm)],[c_509]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1517,plain,
% 11.67/1.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
% 11.67/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.67/1.99      inference(light_normalisation,[status(thm)],[c_1333,c_1420,c_1421]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_2704,plain,
% 11.67/1.99      ( r1_tarski(sK2,sK3) = iProver_top
% 11.67/1.99      | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_1517,c_1339]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4209,plain,
% 11.67/1.99      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top
% 11.67/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_2704,c_3465]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_8,plain,
% 11.67/1.99      ( ~ r1_tarski(X0,X1)
% 11.67/1.99      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 11.67/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1341,plain,
% 11.67/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.67/1.99      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_22,negated_conjecture,
% 11.67/1.99      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 11.67/1.99      | ~ r1_tarski(sK2,sK3) ),
% 11.67/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1334,plain,
% 11.67/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 11.67/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1514,plain,
% 11.67/1.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
% 11.67/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.67/1.99      inference(light_normalisation,[status(thm)],[c_1334,c_1420,c_1421]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_3511,plain,
% 11.67/1.99      ( r1_tarski(sK2,sK3) != iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_1341,c_1514]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4661,plain,
% 11.67/1.99      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top ),
% 11.67/1.99      inference(global_propositional_subsumption,
% 11.67/1.99                [status(thm)],
% 11.67/1.99                [c_4209,c_3511]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4667,plain,
% 11.67/1.99      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = sK3 ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_4661,c_1343]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1,plain,
% 11.67/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.67/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_3510,plain,
% 11.67/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.67/1.99      | r1_tarski(X2,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_1341,c_1339]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_24019,plain,
% 11.67/1.99      ( r1_tarski(X0,X1) != iProver_top
% 11.67/1.99      | r1_tarski(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_0,c_3510]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_25512,plain,
% 11.67/1.99      ( r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = iProver_top
% 11.67/1.99      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_1,c_24019]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_31981,plain,
% 11.67/1.99      ( r1_tarski(k4_xboole_0(sK2,sK1),sK3) != iProver_top
% 11.67/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_4667,c_25512]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4,plain,
% 11.67/1.99      ( r1_tarski(X0,X0) ),
% 11.67/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_77,plain,
% 11.67/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_79,plain,
% 11.67/1.99      ( r1_tarski(sK1,sK1) = iProver_top ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_77]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(contradiction,plain,
% 11.67/1.99      ( $false ),
% 11.67/1.99      inference(minisat,[status(thm)],[c_36639,c_31981,c_3511,c_79]) ).
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.67/1.99  
% 11.67/1.99  ------                               Statistics
% 11.67/1.99  
% 11.67/1.99  ------ General
% 11.67/1.99  
% 11.67/1.99  abstr_ref_over_cycles:                  0
% 11.67/1.99  abstr_ref_under_cycles:                 0
% 11.67/1.99  gc_basic_clause_elim:                   0
% 11.67/1.99  forced_gc_time:                         0
% 11.67/1.99  parsing_time:                           0.008
% 11.67/1.99  unif_index_cands_time:                  0.
% 11.67/1.99  unif_index_add_time:                    0.
% 11.67/1.99  orderings_time:                         0.
% 11.67/1.99  out_proof_time:                         0.009
% 11.67/1.99  total_time:                             1.05
% 11.67/1.99  num_of_symbols:                         44
% 11.67/1.99  num_of_terms:                           40006
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing
% 11.67/1.99  
% 11.67/1.99  num_of_splits:                          0
% 11.67/1.99  num_of_split_atoms:                     0
% 11.67/1.99  num_of_reused_defs:                     0
% 11.67/1.99  num_eq_ax_congr_red:                    15
% 11.67/1.99  num_of_sem_filtered_clauses:            1
% 11.67/1.99  num_of_subtypes:                        0
% 11.67/1.99  monotx_restored_types:                  0
% 11.67/1.99  sat_num_of_epr_types:                   0
% 11.67/1.99  sat_num_of_non_cyclic_types:            0
% 11.67/1.99  sat_guarded_non_collapsed_types:        0
% 11.67/1.99  num_pure_diseq_elim:                    0
% 11.67/1.99  simp_replaced_by:                       0
% 11.67/1.99  res_preprocessed:                       106
% 11.67/1.99  prep_upred:                             0
% 11.67/1.99  prep_unflattend:                        46
% 11.67/1.99  smt_new_axioms:                         0
% 11.67/1.99  pred_elim_cands:                        2
% 11.67/1.99  pred_elim:                              2
% 11.67/1.99  pred_elim_cl:                           3
% 11.67/1.99  pred_elim_cycles:                       5
% 11.67/1.99  merged_defs:                            24
% 11.67/1.99  merged_defs_ncl:                        0
% 11.67/1.99  bin_hyper_res:                          25
% 11.67/1.99  prep_cycles:                            4
% 11.67/1.99  pred_elim_time:                         0.007
% 11.67/1.99  splitting_time:                         0.
% 11.67/1.99  sem_filter_time:                        0.
% 11.67/1.99  monotx_time:                            0.
% 11.67/1.99  subtype_inf_time:                       0.
% 11.67/1.99  
% 11.67/1.99  ------ Problem properties
% 11.67/1.99  
% 11.67/1.99  clauses:                                22
% 11.67/1.99  conjectures:                            2
% 11.67/1.99  epr:                                    3
% 11.67/1.99  horn:                                   20
% 11.67/1.99  ground:                                 4
% 11.67/1.99  unary:                                  7
% 11.67/1.99  binary:                                 12
% 11.67/1.99  lits:                                   40
% 11.67/1.99  lits_eq:                                12
% 11.67/1.99  fd_pure:                                0
% 11.67/1.99  fd_pseudo:                              0
% 11.67/1.99  fd_cond:                                0
% 11.67/1.99  fd_pseudo_cond:                         3
% 11.67/1.99  ac_symbols:                             0
% 11.67/1.99  
% 11.67/1.99  ------ Propositional Solver
% 11.67/1.99  
% 11.67/1.99  prop_solver_calls:                      33
% 11.67/1.99  prop_fast_solver_calls:                 1095
% 11.67/1.99  smt_solver_calls:                       0
% 11.67/1.99  smt_fast_solver_calls:                  0
% 11.67/1.99  prop_num_of_clauses:                    17531
% 11.67/1.99  prop_preprocess_simplified:             23330
% 11.67/1.99  prop_fo_subsumed:                       21
% 11.67/1.99  prop_solver_time:                       0.
% 11.67/1.99  smt_solver_time:                        0.
% 11.67/1.99  smt_fast_solver_time:                   0.
% 11.67/1.99  prop_fast_solver_time:                  0.
% 11.67/1.99  prop_unsat_core_time:                   0.002
% 11.67/1.99  
% 11.67/1.99  ------ QBF
% 11.67/1.99  
% 11.67/1.99  qbf_q_res:                              0
% 11.67/1.99  qbf_num_tautologies:                    0
% 11.67/1.99  qbf_prep_cycles:                        0
% 11.67/1.99  
% 11.67/1.99  ------ BMC1
% 11.67/1.99  
% 11.67/1.99  bmc1_current_bound:                     -1
% 11.67/1.99  bmc1_last_solved_bound:                 -1
% 11.67/1.99  bmc1_unsat_core_size:                   -1
% 11.67/1.99  bmc1_unsat_core_parents_size:           -1
% 11.67/1.99  bmc1_merge_next_fun:                    0
% 11.67/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.67/1.99  
% 11.67/1.99  ------ Instantiation
% 11.67/1.99  
% 11.67/1.99  inst_num_of_clauses:                    3681
% 11.67/1.99  inst_num_in_passive:                    675
% 11.67/1.99  inst_num_in_active:                     1585
% 11.67/1.99  inst_num_in_unprocessed:                1421
% 11.67/1.99  inst_num_of_loops:                      1910
% 11.67/1.99  inst_num_of_learning_restarts:          0
% 11.67/1.99  inst_num_moves_active_passive:          322
% 11.67/1.99  inst_lit_activity:                      0
% 11.67/1.99  inst_lit_activity_moves:                0
% 11.67/1.99  inst_num_tautologies:                   0
% 11.67/1.99  inst_num_prop_implied:                  0
% 11.67/1.99  inst_num_existing_simplified:           0
% 11.67/1.99  inst_num_eq_res_simplified:             0
% 11.67/1.99  inst_num_child_elim:                    0
% 11.67/1.99  inst_num_of_dismatching_blockings:      4167
% 11.67/1.99  inst_num_of_non_proper_insts:           5558
% 11.67/1.99  inst_num_of_duplicates:                 0
% 11.67/1.99  inst_inst_num_from_inst_to_res:         0
% 11.67/1.99  inst_dismatching_checking_time:         0.
% 11.67/1.99  
% 11.67/1.99  ------ Resolution
% 11.67/1.99  
% 11.67/1.99  res_num_of_clauses:                     0
% 11.67/1.99  res_num_in_passive:                     0
% 11.67/1.99  res_num_in_active:                      0
% 11.67/1.99  res_num_of_loops:                       110
% 11.67/1.99  res_forward_subset_subsumed:            281
% 11.67/1.99  res_backward_subset_subsumed:           0
% 11.67/1.99  res_forward_subsumed:                   3
% 11.67/1.99  res_backward_subsumed:                  0
% 11.67/1.99  res_forward_subsumption_resolution:     2
% 11.67/1.99  res_backward_subsumption_resolution:    0
% 11.67/1.99  res_clause_to_clause_subsumption:       14682
% 11.67/1.99  res_orphan_elimination:                 0
% 11.67/1.99  res_tautology_del:                      318
% 11.67/1.99  res_num_eq_res_simplified:              0
% 11.67/1.99  res_num_sel_changes:                    0
% 11.67/1.99  res_moves_from_active_to_pass:          0
% 11.67/1.99  
% 11.67/1.99  ------ Superposition
% 11.67/1.99  
% 11.67/1.99  sup_time_total:                         0.
% 11.67/1.99  sup_time_generating:                    0.
% 11.67/1.99  sup_time_sim_full:                      0.
% 11.67/1.99  sup_time_sim_immed:                     0.
% 11.67/1.99  
% 11.67/1.99  sup_num_of_clauses:                     2320
% 11.67/1.99  sup_num_in_active:                      348
% 11.67/1.99  sup_num_in_passive:                     1972
% 11.67/1.99  sup_num_of_loops:                       380
% 11.67/1.99  sup_fw_superposition:                   1920
% 11.67/1.99  sup_bw_superposition:                   2437
% 11.67/1.99  sup_immediate_simplified:               822
% 11.67/1.99  sup_given_eliminated:                   0
% 11.67/1.99  comparisons_done:                       0
% 11.67/1.99  comparisons_avoided:                    9
% 11.67/1.99  
% 11.67/1.99  ------ Simplifications
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  sim_fw_subset_subsumed:                 50
% 11.67/1.99  sim_bw_subset_subsumed:                 32
% 11.67/1.99  sim_fw_subsumed:                        245
% 11.67/1.99  sim_bw_subsumed:                        26
% 11.67/1.99  sim_fw_subsumption_res:                 0
% 11.67/1.99  sim_bw_subsumption_res:                 0
% 11.67/1.99  sim_tautology_del:                      126
% 11.67/1.99  sim_eq_tautology_del:                   37
% 11.67/1.99  sim_eq_res_simp:                        0
% 11.67/1.99  sim_fw_demodulated:                     390
% 11.67/1.99  sim_bw_demodulated:                     39
% 11.67/1.99  sim_light_normalised:                   186
% 11.67/1.99  sim_joinable_taut:                      0
% 11.67/1.99  sim_joinable_simp:                      0
% 11.67/1.99  sim_ac_normalised:                      0
% 11.67/1.99  sim_smt_subsumption:                    0
% 11.67/1.99  
%------------------------------------------------------------------------------
