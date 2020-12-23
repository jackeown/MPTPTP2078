%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:06 EST 2020

% Result     : Theorem 35.63s
% Output     : CNFRefutation 35.63s
% Verified   : 
% Statistics : Number of formulae       :  170 (1501 expanded)
%              Number of clauses        :  109 ( 590 expanded)
%              Number of leaves         :   24 ( 356 expanded)
%              Depth                    :   20
%              Number of atoms          :  312 (2928 expanded)
%              Number of equality atoms :  202 (1429 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f32,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f38])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f73,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)),k4_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f41,f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f49,f41,f41,f41,f41])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),X0)) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f50,f41,f41])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f41])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_213,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_99193,plain,
    ( X0 != X1
    | X0 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_99194,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) != sK1
    | sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_99193])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_21702,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21707,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_25323,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21702,c_21707])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_12369,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_12370,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12369])).

cnf(c_25998,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25323,c_27,c_33,c_12370])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_21711,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_26003,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_25998,c_21711])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21713,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_26029,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_26003,c_21713])).

cnf(c_4,plain,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)),k4_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X0,X1))) = k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26196,plain,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,sK1),sK2),k4_xboole_0(sK2,k3_xboole_0(X0,sK1))) = k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK2,X0)),sK1) ),
    inference(superposition,[status(thm)],[c_26029,c_4])).

cnf(c_26598,plain,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(sK1,X0),sK2),k4_xboole_0(sK2,k3_xboole_0(sK1,X0))) = k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK2,X0)),sK1) ),
    inference(superposition,[status(thm)],[c_2,c_26196])).

cnf(c_26184,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k3_xboole_0(X0,sK1)),k4_xboole_0(k3_xboole_0(X0,sK1),sK2)) = k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(X0,sK2)),sK1) ),
    inference(superposition,[status(thm)],[c_26029,c_4])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26440,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,sK1),X1),k4_xboole_0(X1,k3_xboole_0(X0,sK1)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,sK1),X1),k4_xboole_0(X1,k3_xboole_0(X0,sK1))),sK2)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(X0,sK2)),sK1),X1),k4_xboole_0(X1,k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(X0,sK2)),sK1))) ),
    inference(superposition,[status(thm)],[c_26184,c_9])).

cnf(c_47611,plain,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(sK1,sK2)),sK1),sK2),k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(sK1,sK2)),sK1))) = k2_xboole_0(k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK1)),k4_xboole_0(k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_26598,c_26440])).

cnf(c_1,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26186,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_26029,c_1])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21984,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22046,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_7])).

cnf(c_0,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_22607,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0),k3_xboole_0(X0,X0)),k4_xboole_0(k3_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0))) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_22046,c_0])).

cnf(c_22616,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X0),k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k1_xboole_0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_22607,c_3,c_21984,c_22046])).

cnf(c_22212,plain,
    ( k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X1) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22046,c_4])).

cnf(c_22218,plain,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k1_xboole_0) = k3_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X1) ),
    inference(light_normalisation,[status(thm)],[c_22212,c_22046])).

cnf(c_22219,plain,
    ( k3_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_22218,c_22046])).

cnf(c_22221,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22219,c_21984])).

cnf(c_22297,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_22221,c_1])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22309,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22297,c_8])).

cnf(c_22300,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22221,c_2])).

cnf(c_22322,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_22300,c_5])).

cnf(c_22320,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22300,c_1])).

cnf(c_22334,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_22320,c_8])).

cnf(c_22617,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_22616,c_22309,c_22322,c_22334])).

cnf(c_26213,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26186,c_21984,c_22046,c_22617])).

cnf(c_47894,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),sK1)),k4_xboole_0(k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),sK1),sK2)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK1),sK2),k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK1))) ),
    inference(light_normalisation,[status(thm)],[c_47611,c_26213])).

cnf(c_26195,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_26029,c_2])).

cnf(c_26393,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_26195,c_0])).

cnf(c_26397,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_26195,c_1])).

cnf(c_26413,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_26393,c_26397])).

cnf(c_21982,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_5])).

cnf(c_26194,plain,
    ( k2_xboole_0(sK1,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_26029,c_21982])).

cnf(c_26415,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_26413,c_26194])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21706,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26853,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_21702,c_21706])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_21705,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_27301,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26853,c_21705])).

cnf(c_27470,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27301,c_27])).

cnf(c_27475,plain,
    ( r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27470,c_21707])).

cnf(c_27983,plain,
    ( r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27475,c_33])).

cnf(c_27988,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_27983,c_21711])).

cnf(c_27995,plain,
    ( k3_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_27988,c_21713])).

cnf(c_28157,plain,
    ( k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)),sK1) = k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_27995,c_26184])).

cnf(c_47895,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_47894,c_3,c_22322,c_22617,c_26184,c_26196,c_26415,c_28157])).

cnf(c_48074,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK2,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK1,sK2)),sK1)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_47895,c_0])).

cnf(c_26395,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k3_xboole_0(X0,sK2)),k4_xboole_0(k3_xboole_0(X0,sK2),sK2)) = k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK1)),sK2) ),
    inference(superposition,[status(thm)],[c_26195,c_4])).

cnf(c_22100,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X1,X0)),k4_xboole_0(k3_xboole_0(X1,X0),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_29772,plain,
    ( k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK1)),sK2) = k4_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_26395,c_22100])).

cnf(c_29777,plain,
    ( k3_xboole_0(k4_xboole_0(sK1,X0),sK2) = k4_xboole_0(sK2,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_29772])).

cnf(c_30451,plain,
    ( k3_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK2,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_29777,c_2])).

cnf(c_48186,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,k3_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK2,k3_xboole_0(sK1,sK2)),sK1)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_48074,c_30451])).

cnf(c_48187,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,sK2)),k4_xboole_0(k4_xboole_0(sK2,sK2),sK1)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_48186,c_26195])).

cnf(c_48188,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_48187,c_22046,c_22309,c_22322,c_22334])).

cnf(c_22153,plain,
    ( X0 != X1
    | X0 = k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
    | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_22379,plain,
    ( X0 != k2_xboole_0(X1,X2)
    | X0 = k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
    | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_22153])).

cnf(c_22539,plain,
    ( X0 != k2_xboole_0(X1,k4_xboole_0(sK1,sK2))
    | X0 = k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
    | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(X1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_22379])).

cnf(c_34092,plain,
    ( X0 = k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
    | X0 != k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_22539])).

cnf(c_34093,plain,
    ( k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | sK1 = k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
    | sK1 != k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_34092])).

cnf(c_214,plain,
    ( X0 != X1
    | X2 != X3
    | k2_xboole_0(X0,X2) = k2_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_22406,plain,
    ( k3_subset_1(sK1,sK2) != X0
    | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k2_xboole_0(X1,X0)
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_22531,plain,
    ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k2_xboole_0(X0,k4_xboole_0(sK1,sK2))
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_22406])).

cnf(c_33414,plain,
    ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_22531])).

cnf(c_33415,plain,
    ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(equality_resolution_simp,[status(thm)],[c_33414])).

cnf(c_19513,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_12826,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12829,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_12827,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14271,plain,
    ( k4_subset_1(sK1,sK2,X0) = k2_xboole_0(sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12826,c_12827])).

cnf(c_15054,plain,
    ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,X0)) = k2_xboole_0(sK2,k3_subset_1(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12829,c_14271])).

cnf(c_16310,plain,
    ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) = k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_12826,c_15054])).

cnf(c_6200,plain,
    ( X0 != X1
    | k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != X1
    | k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_6214,plain,
    ( X0 != k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
    | k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) = X0
    | k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6200])).

cnf(c_6215,plain,
    ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
    | k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) = sK1
    | sK1 != k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6214])).

cnf(c_25,negated_conjecture,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_20,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1280,plain,
    ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != sK1 ),
    inference(demodulation,[status(thm)],[c_25,c_20])).

cnf(c_212,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_238,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_99194,c_48188,c_34093,c_33415,c_19513,c_16310,c_6215,c_1280,c_238,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 35.63/4.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.63/4.99  
% 35.63/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.63/4.99  
% 35.63/4.99  ------  iProver source info
% 35.63/4.99  
% 35.63/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.63/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.63/4.99  git: non_committed_changes: false
% 35.63/4.99  git: last_make_outside_of_git: false
% 35.63/4.99  
% 35.63/4.99  ------ 
% 35.63/4.99  ------ Parsing...
% 35.63/4.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  ------ Proving...
% 35.63/4.99  ------ Problem Properties 
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  clauses                                 27
% 35.63/4.99  conjectures                             2
% 35.63/4.99  EPR                                     4
% 35.63/4.99  Horn                                    24
% 35.63/4.99  unary                                   15
% 35.63/4.99  binary                                  5
% 35.63/4.99  lits                                    46
% 35.63/4.99  lits eq                                 18
% 35.63/4.99  fd_pure                                 0
% 35.63/4.99  fd_pseudo                               0
% 35.63/4.99  fd_cond                                 0
% 35.63/4.99  fd_pseudo_cond                          2
% 35.63/4.99  AC symbols                              0
% 35.63/4.99  
% 35.63/4.99  ------ Input Options Time Limit: Unbounded
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 35.63/4.99  Current options:
% 35.63/4.99  ------ 
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.63/4.99  
% 35.63/4.99  ------ Proving...
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  % SZS status Theorem for theBenchmark.p
% 35.63/4.99  
% 35.63/4.99  % SZS output start CNFRefutation for theBenchmark.p
% 35.63/4.99  
% 35.63/4.99  fof(f1,axiom,(
% 35.63/4.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f40,plain,(
% 35.63/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.63/4.99    inference(cnf_transformation,[],[f1])).
% 35.63/4.99  
% 35.63/4.99  fof(f23,conjecture,(
% 35.63/4.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f24,negated_conjecture,(
% 35.63/4.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 35.63/4.99    inference(negated_conjecture,[],[f23])).
% 35.63/4.99  
% 35.63/4.99  fof(f32,plain,(
% 35.63/4.99    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.63/4.99    inference(ennf_transformation,[],[f24])).
% 35.63/4.99  
% 35.63/4.99  fof(f38,plain,(
% 35.63/4.99    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 35.63/4.99    introduced(choice_axiom,[])).
% 35.63/4.99  
% 35.63/4.99  fof(f39,plain,(
% 35.63/4.99    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 35.63/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f38])).
% 35.63/4.99  
% 35.63/4.99  fof(f68,plain,(
% 35.63/4.99    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 35.63/4.99    inference(cnf_transformation,[],[f39])).
% 35.63/4.99  
% 35.63/4.99  fof(f17,axiom,(
% 35.63/4.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f27,plain,(
% 35.63/4.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 35.63/4.99    inference(ennf_transformation,[],[f17])).
% 35.63/4.99  
% 35.63/4.99  fof(f37,plain,(
% 35.63/4.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 35.63/4.99    inference(nnf_transformation,[],[f27])).
% 35.63/4.99  
% 35.63/4.99  fof(f59,plain,(
% 35.63/4.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 35.63/4.99    inference(cnf_transformation,[],[f37])).
% 35.63/4.99  
% 35.63/4.99  fof(f21,axiom,(
% 35.63/4.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f66,plain,(
% 35.63/4.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 35.63/4.99    inference(cnf_transformation,[],[f21])).
% 35.63/4.99  
% 35.63/4.99  fof(f15,axiom,(
% 35.63/4.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f33,plain,(
% 35.63/4.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 35.63/4.99    inference(nnf_transformation,[],[f15])).
% 35.63/4.99  
% 35.63/4.99  fof(f34,plain,(
% 35.63/4.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 35.63/4.99    inference(rectify,[],[f33])).
% 35.63/4.99  
% 35.63/4.99  fof(f35,plain,(
% 35.63/4.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 35.63/4.99    introduced(choice_axiom,[])).
% 35.63/4.99  
% 35.63/4.99  fof(f36,plain,(
% 35.63/4.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 35.63/4.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 35.63/4.99  
% 35.63/4.99  fof(f54,plain,(
% 35.63/4.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 35.63/4.99    inference(cnf_transformation,[],[f36])).
% 35.63/4.99  
% 35.63/4.99  fof(f79,plain,(
% 35.63/4.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 35.63/4.99    inference(equality_resolution,[],[f54])).
% 35.63/4.99  
% 35.63/4.99  fof(f7,axiom,(
% 35.63/4.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f26,plain,(
% 35.63/4.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.63/4.99    inference(ennf_transformation,[],[f7])).
% 35.63/4.99  
% 35.63/4.99  fof(f46,plain,(
% 35.63/4.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.63/4.99    inference(cnf_transformation,[],[f26])).
% 35.63/4.99  
% 35.63/4.99  fof(f5,axiom,(
% 35.63/4.99    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f44,plain,(
% 35.63/4.99    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 35.63/4.99    inference(cnf_transformation,[],[f5])).
% 35.63/4.99  
% 35.63/4.99  fof(f2,axiom,(
% 35.63/4.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f41,plain,(
% 35.63/4.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 35.63/4.99    inference(cnf_transformation,[],[f2])).
% 35.63/4.99  
% 35.63/4.99  fof(f73,plain,(
% 35.63/4.99    ( ! [X2,X0,X1] : (k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)),k4_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X0,X1)))) )),
% 35.63/4.99    inference(definition_unfolding,[],[f44,f41,f41])).
% 35.63/4.99  
% 35.63/4.99  fof(f10,axiom,(
% 35.63/4.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f49,plain,(
% 35.63/4.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 35.63/4.99    inference(cnf_transformation,[],[f10])).
% 35.63/4.99  
% 35.63/4.99  fof(f75,plain,(
% 35.63/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) )),
% 35.63/4.99    inference(definition_unfolding,[],[f49,f41,f41,f41,f41])).
% 35.63/4.99  
% 35.63/4.99  fof(f4,axiom,(
% 35.63/4.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f43,plain,(
% 35.63/4.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 35.63/4.99    inference(cnf_transformation,[],[f4])).
% 35.63/4.99  
% 35.63/4.99  fof(f72,plain,(
% 35.63/4.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),X0))) )),
% 35.63/4.99    inference(definition_unfolding,[],[f43,f41])).
% 35.63/4.99  
% 35.63/4.99  fof(f3,axiom,(
% 35.63/4.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f25,plain,(
% 35.63/4.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 35.63/4.99    inference(rectify,[],[f3])).
% 35.63/4.99  
% 35.63/4.99  fof(f42,plain,(
% 35.63/4.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 35.63/4.99    inference(cnf_transformation,[],[f25])).
% 35.63/4.99  
% 35.63/4.99  fof(f6,axiom,(
% 35.63/4.99    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f45,plain,(
% 35.63/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 35.63/4.99    inference(cnf_transformation,[],[f6])).
% 35.63/4.99  
% 35.63/4.99  fof(f8,axiom,(
% 35.63/4.99    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f47,plain,(
% 35.63/4.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 35.63/4.99    inference(cnf_transformation,[],[f8])).
% 35.63/4.99  
% 35.63/4.99  fof(f11,axiom,(
% 35.63/4.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f50,plain,(
% 35.63/4.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 35.63/4.99    inference(cnf_transformation,[],[f11])).
% 35.63/4.99  
% 35.63/4.99  fof(f71,plain,(
% 35.63/4.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))))) )),
% 35.63/4.99    inference(definition_unfolding,[],[f50,f41,f41])).
% 35.63/4.99  
% 35.63/4.99  fof(f9,axiom,(
% 35.63/4.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f48,plain,(
% 35.63/4.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.63/4.99    inference(cnf_transformation,[],[f9])).
% 35.63/4.99  
% 35.63/4.99  fof(f74,plain,(
% 35.63/4.99    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 35.63/4.99    inference(definition_unfolding,[],[f48,f41])).
% 35.63/4.99  
% 35.63/4.99  fof(f19,axiom,(
% 35.63/4.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f28,plain,(
% 35.63/4.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.63/4.99    inference(ennf_transformation,[],[f19])).
% 35.63/4.99  
% 35.63/4.99  fof(f64,plain,(
% 35.63/4.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.63/4.99    inference(cnf_transformation,[],[f28])).
% 35.63/4.99  
% 35.63/4.99  fof(f20,axiom,(
% 35.63/4.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f29,plain,(
% 35.63/4.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.63/4.99    inference(ennf_transformation,[],[f20])).
% 35.63/4.99  
% 35.63/4.99  fof(f65,plain,(
% 35.63/4.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.63/4.99    inference(cnf_transformation,[],[f29])).
% 35.63/4.99  
% 35.63/4.99  fof(f22,axiom,(
% 35.63/4.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f30,plain,(
% 35.63/4.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 35.63/4.99    inference(ennf_transformation,[],[f22])).
% 35.63/4.99  
% 35.63/4.99  fof(f31,plain,(
% 35.63/4.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.63/4.99    inference(flattening,[],[f30])).
% 35.63/4.99  
% 35.63/4.99  fof(f67,plain,(
% 35.63/4.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.63/4.99    inference(cnf_transformation,[],[f31])).
% 35.63/4.99  
% 35.63/4.99  fof(f69,plain,(
% 35.63/4.99    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))),
% 35.63/4.99    inference(cnf_transformation,[],[f39])).
% 35.63/4.99  
% 35.63/4.99  fof(f18,axiom,(
% 35.63/4.99    ! [X0] : k2_subset_1(X0) = X0),
% 35.63/4.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.63/4.99  
% 35.63/4.99  fof(f63,plain,(
% 35.63/4.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 35.63/4.99    inference(cnf_transformation,[],[f18])).
% 35.63/4.99  
% 35.63/4.99  cnf(c_213,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_99193,plain,
% 35.63/4.99      ( X0 != X1
% 35.63/4.99      | X0 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
% 35.63/4.99      | k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) != X1 ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_213]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_99194,plain,
% 35.63/4.99      ( k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) != sK1
% 35.63/4.99      | sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
% 35.63/4.99      | sK1 != sK1 ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_99193]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_2,plain,
% 35.63/4.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.63/4.99      inference(cnf_transformation,[],[f40]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26,negated_conjecture,
% 35.63/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 35.63/4.99      inference(cnf_transformation,[],[f68]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_21702,plain,
% 35.63/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_19,plain,
% 35.63/4.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 35.63/4.99      inference(cnf_transformation,[],[f59]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_21707,plain,
% 35.63/4.99      ( m1_subset_1(X0,X1) != iProver_top
% 35.63/4.99      | r2_hidden(X0,X1) = iProver_top
% 35.63/4.99      | v1_xboole_0(X1) = iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_25323,plain,
% 35.63/4.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 35.63/4.99      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_21702,c_21707]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_27,plain,
% 35.63/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_23,plain,
% 35.63/4.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 35.63/4.99      inference(cnf_transformation,[],[f66]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_31,plain,
% 35.63/4.99      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_33,plain,
% 35.63/4.99      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_31]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_12369,plain,
% 35.63/4.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 35.63/4.99      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 35.63/4.99      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_19]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_12370,plain,
% 35.63/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 35.63/4.99      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 35.63/4.99      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_12369]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_25998,plain,
% 35.63/4.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 35.63/4.99      inference(global_propositional_subsumption,
% 35.63/4.99                [status(thm)],
% 35.63/4.99                [c_25323,c_27,c_33,c_12370]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_14,plain,
% 35.63/4.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.63/4.99      inference(cnf_transformation,[],[f79]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_21711,plain,
% 35.63/4.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.63/4.99      | r1_tarski(X0,X1) = iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26003,plain,
% 35.63/4.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_25998,c_21711]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_6,plain,
% 35.63/4.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 35.63/4.99      inference(cnf_transformation,[],[f46]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_21713,plain,
% 35.63/4.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26029,plain,
% 35.63/4.99      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26003,c_21713]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_4,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)),k4_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X0,X1))) = k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X2,X0)),X1) ),
% 35.63/4.99      inference(cnf_transformation,[],[f73]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26196,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,sK1),sK2),k4_xboole_0(sK2,k3_xboole_0(X0,sK1))) = k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK2,X0)),sK1) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26029,c_4]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26598,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(sK1,X0),sK2),k4_xboole_0(sK2,k3_xboole_0(sK1,X0))) = k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK2,X0)),sK1) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_2,c_26196]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26184,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(sK2,k3_xboole_0(X0,sK1)),k4_xboole_0(k3_xboole_0(X0,sK1),sK2)) = k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(X0,sK2)),sK1) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26029,c_4]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_9,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X0)) ),
% 35.63/4.99      inference(cnf_transformation,[],[f75]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26440,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,sK1),X1),k4_xboole_0(X1,k3_xboole_0(X0,sK1)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,sK1),X1),k4_xboole_0(X1,k3_xboole_0(X0,sK1))),sK2)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(X0,sK2)),sK1),X1),k4_xboole_0(X1,k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(X0,sK2)),sK1))) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26184,c_9]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_47611,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(sK1,sK2)),sK1),sK2),k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK1),k4_xboole_0(sK1,sK2)),sK1))) = k2_xboole_0(k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK1)),k4_xboole_0(k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK1),sK2)) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26598,c_26440]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_1,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 35.63/4.99      inference(cnf_transformation,[],[f72]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26186,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,sK1) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26029,c_1]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_3,plain,
% 35.63/4.99      ( k3_xboole_0(X0,X0) = X0 ),
% 35.63/4.99      inference(cnf_transformation,[],[f42]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_5,plain,
% 35.63/4.99      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 35.63/4.99      inference(cnf_transformation,[],[f45]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_21984,plain,
% 35.63/4.99      ( k2_xboole_0(X0,X0) = X0 ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_7,plain,
% 35.63/4.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 35.63/4.99      inference(cnf_transformation,[],[f47]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22046,plain,
% 35.63/4.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_5,c_7]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_0,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(X0,X1) ),
% 35.63/4.99      inference(cnf_transformation,[],[f71]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22607,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0),k3_xboole_0(X0,X0)),k4_xboole_0(k3_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0))) = k2_xboole_0(X0,X0) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_22046,c_0]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22616,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X0),k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k1_xboole_0))) = X0 ),
% 35.63/4.99      inference(light_normalisation,
% 35.63/4.99                [status(thm)],
% 35.63/4.99                [c_22607,c_3,c_21984,c_22046]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22212,plain,
% 35.63/4.99      ( k3_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),X1) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k1_xboole_0) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_22046,c_4]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22218,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k1_xboole_0) = k3_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X1) ),
% 35.63/4.99      inference(light_normalisation,[status(thm)],[c_22212,c_22046]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22219,plain,
% 35.63/4.99      ( k3_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0),X0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 35.63/4.99      inference(demodulation,[status(thm)],[c_22218,c_22046]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22221,plain,
% 35.63/4.99      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.63/4.99      inference(demodulation,[status(thm)],[c_22219,c_21984]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22297,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_22221,c_1]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_8,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 35.63/4.99      inference(cnf_transformation,[],[f74]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22309,plain,
% 35.63/4.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.63/4.99      inference(demodulation,[status(thm)],[c_22297,c_8]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22300,plain,
% 35.63/4.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_22221,c_2]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22322,plain,
% 35.63/4.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_22300,c_5]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22320,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_22300,c_1]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22334,plain,
% 35.63/4.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.63/4.99      inference(light_normalisation,[status(thm)],[c_22320,c_8]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22617,plain,
% 35.63/4.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 35.63/4.99      inference(demodulation,
% 35.63/4.99                [status(thm)],
% 35.63/4.99                [c_22616,c_22309,c_22322,c_22334]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26213,plain,
% 35.63/4.99      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 35.63/4.99      inference(demodulation,
% 35.63/4.99                [status(thm)],
% 35.63/4.99                [c_26186,c_21984,c_22046,c_22617]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_47894,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),sK1)),k4_xboole_0(k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),sK1),sK2)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK1),sK2),k4_xboole_0(sK2,k3_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)),sK1))) ),
% 35.63/4.99      inference(light_normalisation,[status(thm)],[c_47611,c_26213]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26195,plain,
% 35.63/4.99      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26029,c_2]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26393,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)),sK2),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))) = k2_xboole_0(sK1,sK2) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26195,c_0]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26397,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)) = k4_xboole_0(sK1,sK2) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26195,c_1]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26413,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
% 35.63/4.99      inference(light_normalisation,[status(thm)],[c_26393,c_26397]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_21982,plain,
% 35.63/4.99      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_2,c_5]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26194,plain,
% 35.63/4.99      ( k2_xboole_0(sK1,sK2) = sK1 ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26029,c_21982]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26415,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = sK1 ),
% 35.63/4.99      inference(light_normalisation,[status(thm)],[c_26413,c_26194]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_21,plain,
% 35.63/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.63/4.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 35.63/4.99      inference(cnf_transformation,[],[f64]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_21706,plain,
% 35.63/4.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 35.63/4.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26853,plain,
% 35.63/4.99      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_21702,c_21706]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22,plain,
% 35.63/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.63/4.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 35.63/4.99      inference(cnf_transformation,[],[f65]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_21705,plain,
% 35.63/4.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.63/4.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_27301,plain,
% 35.63/4.99      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 35.63/4.99      | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26853,c_21705]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_27470,plain,
% 35.63/4.99      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 35.63/4.99      inference(global_propositional_subsumption,
% 35.63/4.99                [status(thm)],
% 35.63/4.99                [c_27301,c_27]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_27475,plain,
% 35.63/4.99      ( r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top
% 35.63/4.99      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_27470,c_21707]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_27983,plain,
% 35.63/4.99      ( r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 35.63/4.99      inference(global_propositional_subsumption,
% 35.63/4.99                [status(thm)],
% 35.63/4.99                [c_27475,c_33]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_27988,plain,
% 35.63/4.99      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) = iProver_top ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_27983,c_21711]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_27995,plain,
% 35.63/4.99      ( k3_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k4_xboole_0(sK1,sK2) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_27988,c_21713]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_28157,plain,
% 35.63/4.99      ( k3_xboole_0(k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)),sK1) = k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_27995,c_26184]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_47895,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,sK2),sK2)) = sK1 ),
% 35.63/4.99      inference(demodulation,
% 35.63/4.99                [status(thm)],
% 35.63/4.99                [c_47894,c_3,c_22322,c_22617,c_26184,c_26196,c_26415,
% 35.63/4.99                 c_28157]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_48074,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK2,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK1,sK2)),sK1)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_47895,c_0]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_26395,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(sK2,k3_xboole_0(X0,sK2)),k4_xboole_0(k3_xboole_0(X0,sK2),sK2)) = k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK1)),sK2) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_26195,c_4]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22100,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X1,X0)),k4_xboole_0(k3_xboole_0(X1,X0),X0)) = k4_xboole_0(X0,X1) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_29772,plain,
% 35.63/4.99      ( k3_xboole_0(k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK1)),sK2) = k4_xboole_0(sK2,X0) ),
% 35.63/4.99      inference(demodulation,[status(thm)],[c_26395,c_22100]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_29777,plain,
% 35.63/4.99      ( k3_xboole_0(k4_xboole_0(sK1,X0),sK2) = k4_xboole_0(sK2,k3_xboole_0(sK1,X0)) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_1,c_29772]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_30451,plain,
% 35.63/4.99      ( k3_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK2,k3_xboole_0(sK1,X0)) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_29777,c_2]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_48186,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,k3_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK2,k3_xboole_0(sK1,sK2)),sK1)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
% 35.63/4.99      inference(demodulation,[status(thm)],[c_48074,c_30451]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_48187,plain,
% 35.63/4.99      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK2,sK2)),k4_xboole_0(k4_xboole_0(sK2,sK2),sK1)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
% 35.63/4.99      inference(light_normalisation,[status(thm)],[c_48186,c_26195]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_48188,plain,
% 35.63/4.99      ( k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
% 35.63/4.99      inference(demodulation,
% 35.63/4.99                [status(thm)],
% 35.63/4.99                [c_48187,c_22046,c_22309,c_22322,c_22334]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22153,plain,
% 35.63/4.99      ( X0 != X1
% 35.63/4.99      | X0 = k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
% 35.63/4.99      | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) != X1 ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_213]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22379,plain,
% 35.63/4.99      ( X0 != k2_xboole_0(X1,X2)
% 35.63/4.99      | X0 = k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
% 35.63/4.99      | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(X1,X2) ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_22153]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22539,plain,
% 35.63/4.99      ( X0 != k2_xboole_0(X1,k4_xboole_0(sK1,sK2))
% 35.63/4.99      | X0 = k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
% 35.63/4.99      | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(X1,k4_xboole_0(sK1,sK2)) ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_22379]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_34092,plain,
% 35.63/4.99      ( X0 = k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
% 35.63/4.99      | X0 != k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
% 35.63/4.99      | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_22539]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_34093,plain,
% 35.63/4.99      ( k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
% 35.63/4.99      | sK1 = k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
% 35.63/4.99      | sK1 != k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_34092]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_214,plain,
% 35.63/4.99      ( X0 != X1 | X2 != X3 | k2_xboole_0(X0,X2) = k2_xboole_0(X1,X3) ),
% 35.63/4.99      theory(equality) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22406,plain,
% 35.63/4.99      ( k3_subset_1(sK1,sK2) != X0
% 35.63/4.99      | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k2_xboole_0(X1,X0)
% 35.63/4.99      | sK2 != X1 ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_214]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_22531,plain,
% 35.63/4.99      ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
% 35.63/4.99      | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k2_xboole_0(X0,k4_xboole_0(sK1,sK2))
% 35.63/4.99      | sK2 != X0 ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_22406]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_33414,plain,
% 35.63/4.99      ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
% 35.63/4.99      | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
% 35.63/4.99      | sK2 != sK2 ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_22531]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_33415,plain,
% 35.63/4.99      ( k3_subset_1(sK1,sK2) != k4_xboole_0(sK1,sK2)
% 35.63/4.99      | k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
% 35.63/4.99      inference(equality_resolution_simp,[status(thm)],[c_33414]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_19513,plain,
% 35.63/4.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 35.63/4.99      | k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_21]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_12826,plain,
% 35.63/4.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_12829,plain,
% 35.63/4.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.63/4.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_24,plain,
% 35.63/4.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.63/4.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.63/4.99      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 35.63/4.99      inference(cnf_transformation,[],[f67]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_12827,plain,
% 35.63/4.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 35.63/4.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 35.63/4.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 35.63/4.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_14271,plain,
% 35.63/4.99      ( k4_subset_1(sK1,sK2,X0) = k2_xboole_0(sK2,X0)
% 35.63/4.99      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_12826,c_12827]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_15054,plain,
% 35.63/4.99      ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,X0)) = k2_xboole_0(sK2,k3_subset_1(sK1,X0))
% 35.63/4.99      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_12829,c_14271]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_16310,plain,
% 35.63/4.99      ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) = k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
% 35.63/4.99      inference(superposition,[status(thm)],[c_12826,c_15054]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_6200,plain,
% 35.63/4.99      ( X0 != X1
% 35.63/4.99      | k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != X1
% 35.63/4.99      | k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) = X0 ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_213]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_6214,plain,
% 35.63/4.99      ( X0 != k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
% 35.63/4.99      | k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) = X0
% 35.63/4.99      | k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_6200]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_6215,plain,
% 35.63/4.99      ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != k2_xboole_0(sK2,k3_subset_1(sK1,sK2))
% 35.63/4.99      | k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) = sK1
% 35.63/4.99      | sK1 != k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_6214]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_25,negated_conjecture,
% 35.63/4.99      ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
% 35.63/4.99      inference(cnf_transformation,[],[f69]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_20,plain,
% 35.63/4.99      ( k2_subset_1(X0) = X0 ),
% 35.63/4.99      inference(cnf_transformation,[],[f63]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_1280,plain,
% 35.63/4.99      ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != sK1 ),
% 35.63/4.99      inference(demodulation,[status(thm)],[c_25,c_20]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_212,plain,( X0 = X0 ),theory(equality) ).
% 35.63/4.99  
% 35.63/4.99  cnf(c_238,plain,
% 35.63/4.99      ( sK1 = sK1 ),
% 35.63/4.99      inference(instantiation,[status(thm)],[c_212]) ).
% 35.63/4.99  
% 35.63/4.99  cnf(contradiction,plain,
% 35.63/4.99      ( $false ),
% 35.63/4.99      inference(minisat,
% 35.63/4.99                [status(thm)],
% 35.63/4.99                [c_99194,c_48188,c_34093,c_33415,c_19513,c_16310,c_6215,
% 35.63/4.99                 c_1280,c_238,c_26]) ).
% 35.63/4.99  
% 35.63/4.99  
% 35.63/4.99  % SZS output end CNFRefutation for theBenchmark.p
% 35.63/4.99  
% 35.63/4.99  ------                               Statistics
% 35.63/4.99  
% 35.63/4.99  ------ Selected
% 35.63/4.99  
% 35.63/4.99  total_time:                             4.145
% 35.63/4.99  
%------------------------------------------------------------------------------
