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
% DateTime   : Thu Dec  3 11:36:37 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 482 expanded)
%              Number of clauses        :   69 ( 177 expanded)
%              Number of leaves         :   13 (  95 expanded)
%              Depth                    :   23
%              Number of atoms          :  322 (1695 expanded)
%              Number of equality atoms :  136 ( 527 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
     => r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))
       => r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ~ r3_xboole_0(X0,X1)
        & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) )
   => ( ~ r3_xboole_0(sK2,sK3)
      & k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) = k1_zfmisc_1(k2_xboole_0(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r3_xboole_0(sK2,sK3)
    & k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) = k1_zfmisc_1(k2_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f39])).

fof(f70,plain,(
    k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) = k1_zfmisc_1(k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) )
     => r3_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ( ~ r1_tarski(X1,X0)
        & ~ r1_tarski(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ~ r3_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3709,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3818,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3709])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3708,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) = k1_zfmisc_1(k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3713,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4406,plain,
    ( r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK2,sK3))) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_3713])).

cnf(c_4446,plain,
    ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3708,c_4406])).

cnf(c_4644,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3818,c_4446])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3711,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4642,plain,
    ( r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3711,c_4446])).

cnf(c_26,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3707,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4710,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),sK3) = iProver_top
    | r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4642,c_3707])).

cnf(c_4750,plain,
    ( r1_tarski(k2_xboole_0(sK2,sK3),sK3) = iProver_top
    | r1_tarski(k2_xboole_0(sK2,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4710,c_3707])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3706,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3858,plain,
    ( r1_tarski(k1_zfmisc_1(sK3),k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_3818])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3712,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4226,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK3)
    | r1_tarski(k1_zfmisc_1(k2_xboole_0(sK2,sK3)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3858,c_3712])).

cnf(c_4285,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK3)
    | r1_tarski(k2_xboole_0(sK2,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3706,c_4226])).

cnf(c_17925,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK3)
    | r1_tarski(k2_xboole_0(sK2,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4750,c_4285])).

cnf(c_3821,plain,
    ( r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_3709])).

cnf(c_4225,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
    | r1_tarski(k1_zfmisc_1(k2_xboole_0(sK2,sK3)),k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3821,c_3712])).

cnf(c_4270,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
    | r1_tarski(k2_xboole_0(sK2,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3706,c_4225])).

cnf(c_18113,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK3)
    | k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2) ),
    inference(superposition,[status(thm)],[c_17925,c_4270])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3710,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3888,plain,
    ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(X1)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3706,c_3710])).

cnf(c_4812,plain,
    ( k2_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK3)),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))) = k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_3858,c_3888])).

cnf(c_5036,plain,
    ( r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK3)),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4812,c_3709])).

cnf(c_5100,plain,
    ( k2_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))))) = k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))) ),
    inference(superposition,[status(thm)],[c_5036,c_3888])).

cnf(c_18224,plain,
    ( k2_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3)))) = k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))))
    | k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2) ),
    inference(superposition,[status(thm)],[c_18113,c_5100])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18325,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
    | k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))) = k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(demodulation,[status(thm)],[c_18224,c_7])).

cnf(c_13,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,negated_conjecture,
    ( ~ r3_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_286,plain,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_287,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_4643,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3709,c_4446])).

cnf(c_37,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_39,plain,
    ( r1_tarski(sK2,sK2) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_65,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_67,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_4679,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4643,c_39,c_67])).

cnf(c_3890,plain,
    ( k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = k1_zfmisc_1(k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3821,c_3710])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3714,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4159,plain,
    ( r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3890,c_3714])).

cnf(c_18238,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
    | r2_hidden(X0,k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18113,c_4159])).

cnf(c_19047,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
    | r2_hidden(sK2,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4679,c_18238])).

cnf(c_19105,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_19047,c_3707])).

cnf(c_19253,plain,
    ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18325,c_287,c_19105])).

cnf(c_3891,plain,
    ( k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = k1_zfmisc_1(k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3858,c_3710])).

cnf(c_4160,plain,
    ( r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3891,c_3714])).

cnf(c_19337,plain,
    ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19253,c_4160])).

cnf(c_20981,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4644,c_19337])).

cnf(c_21009,plain,
    ( r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_20981,c_3707])).

cnf(c_12,plain,
    ( r3_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_292,plain,
    ( ~ r1_tarski(X0,X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_293,plain,
    ( ~ r1_tarski(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_294,plain,
    ( r1_tarski(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21009,c_294])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.89/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.89/1.52  
% 7.89/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.89/1.52  
% 7.89/1.52  ------  iProver source info
% 7.89/1.52  
% 7.89/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.89/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.89/1.52  git: non_committed_changes: false
% 7.89/1.52  git: last_make_outside_of_git: false
% 7.89/1.52  
% 7.89/1.52  ------ 
% 7.89/1.52  ------ Parsing...
% 7.89/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  ------ Proving...
% 7.89/1.52  ------ Problem Properties 
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  clauses                                 28
% 7.89/1.52  conjectures                             1
% 7.89/1.52  EPR                                     4
% 7.89/1.52  Horn                                    25
% 7.89/1.52  unary                                   15
% 7.89/1.52  binary                                  6
% 7.89/1.52  lits                                    49
% 7.89/1.52  lits eq                                 17
% 7.89/1.52  fd_pure                                 0
% 7.89/1.52  fd_pseudo                               0
% 7.89/1.52  fd_cond                                 0
% 7.89/1.52  fd_pseudo_cond                          6
% 7.89/1.52  AC symbols                              0
% 7.89/1.52  
% 7.89/1.52  ------ Input Options Time Limit: Unbounded
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.89/1.52  Current options:
% 7.89/1.52  ------ 
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing...
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing...
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.89/1.52  
% 7.89/1.52  ------ Proving...
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  % SZS status Theorem for theBenchmark.p
% 7.89/1.52  
% 7.89/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.89/1.52  
% 7.89/1.52  fof(f1,axiom,(
% 7.89/1.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.89/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.52  
% 7.89/1.52  fof(f41,plain,(
% 7.89/1.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.89/1.52    inference(cnf_transformation,[],[f1])).
% 7.89/1.52  
% 7.89/1.52  fof(f16,axiom,(
% 7.89/1.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.89/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.52  
% 7.89/1.52  fof(f64,plain,(
% 7.89/1.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.89/1.52    inference(cnf_transformation,[],[f16])).
% 7.89/1.52  
% 7.89/1.52  fof(f17,axiom,(
% 7.89/1.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.89/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.52  
% 7.89/1.52  fof(f35,plain,(
% 7.89/1.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.89/1.52    inference(nnf_transformation,[],[f17])).
% 7.89/1.52  
% 7.89/1.52  fof(f36,plain,(
% 7.89/1.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.89/1.52    inference(rectify,[],[f35])).
% 7.89/1.52  
% 7.89/1.52  fof(f37,plain,(
% 7.89/1.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.89/1.52    introduced(choice_axiom,[])).
% 7.89/1.52  
% 7.89/1.52  fof(f38,plain,(
% 7.89/1.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.89/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 7.89/1.52  
% 7.89/1.52  fof(f66,plain,(
% 7.89/1.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.89/1.52    inference(cnf_transformation,[],[f38])).
% 7.89/1.52  
% 7.89/1.52  fof(f81,plain,(
% 7.89/1.52    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.89/1.52    inference(equality_resolution,[],[f66])).
% 7.89/1.52  
% 7.89/1.52  fof(f19,conjecture,(
% 7.89/1.52    ! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 7.89/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.52  
% 7.89/1.52  fof(f20,negated_conjecture,(
% 7.89/1.52    ~! [X0,X1] : (k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)) => r3_xboole_0(X0,X1))),
% 7.89/1.52    inference(negated_conjecture,[],[f19])).
% 7.89/1.52  
% 7.89/1.52  fof(f27,plain,(
% 7.89/1.52    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 7.89/1.52    inference(ennf_transformation,[],[f20])).
% 7.89/1.52  
% 7.89/1.52  fof(f39,plain,(
% 7.89/1.52    ? [X0,X1] : (~r3_xboole_0(X0,X1) & k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(k2_xboole_0(X0,X1))) => (~r3_xboole_0(sK2,sK3) & k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) = k1_zfmisc_1(k2_xboole_0(sK2,sK3)))),
% 7.89/1.52    introduced(choice_axiom,[])).
% 7.89/1.52  
% 7.89/1.52  fof(f40,plain,(
% 7.89/1.52    ~r3_xboole_0(sK2,sK3) & k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) = k1_zfmisc_1(k2_xboole_0(sK2,sK3))),
% 7.89/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f39])).
% 7.89/1.52  
% 7.89/1.52  fof(f70,plain,(
% 7.89/1.52    k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) = k1_zfmisc_1(k2_xboole_0(sK2,sK3))),
% 7.89/1.52    inference(cnf_transformation,[],[f40])).
% 7.89/1.52  
% 7.89/1.52  fof(f2,axiom,(
% 7.89/1.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.89/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.52  
% 7.89/1.52  fof(f28,plain,(
% 7.89/1.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.89/1.52    inference(nnf_transformation,[],[f2])).
% 7.89/1.52  
% 7.89/1.52  fof(f29,plain,(
% 7.89/1.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.89/1.52    inference(flattening,[],[f28])).
% 7.89/1.52  
% 7.89/1.52  fof(f30,plain,(
% 7.89/1.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.89/1.52    inference(rectify,[],[f29])).
% 7.89/1.52  
% 7.89/1.52  fof(f31,plain,(
% 7.89/1.52    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.89/1.52    introduced(choice_axiom,[])).
% 7.89/1.52  
% 7.89/1.52  fof(f32,plain,(
% 7.89/1.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.89/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.89/1.52  
% 7.89/1.52  fof(f42,plain,(
% 7.89/1.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 7.89/1.52    inference(cnf_transformation,[],[f32])).
% 7.89/1.52  
% 7.89/1.52  fof(f78,plain,(
% 7.89/1.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 7.89/1.52    inference(equality_resolution,[],[f42])).
% 7.89/1.52  
% 7.89/1.52  fof(f5,axiom,(
% 7.89/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.89/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.52  
% 7.89/1.52  fof(f33,plain,(
% 7.89/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.89/1.52    inference(nnf_transformation,[],[f5])).
% 7.89/1.52  
% 7.89/1.52  fof(f34,plain,(
% 7.89/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.89/1.52    inference(flattening,[],[f33])).
% 7.89/1.52  
% 7.89/1.52  fof(f50,plain,(
% 7.89/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.89/1.52    inference(cnf_transformation,[],[f34])).
% 7.89/1.52  
% 7.89/1.52  fof(f80,plain,(
% 7.89/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.89/1.52    inference(equality_resolution,[],[f50])).
% 7.89/1.52  
% 7.89/1.52  fof(f65,plain,(
% 7.89/1.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.89/1.52    inference(cnf_transformation,[],[f38])).
% 7.89/1.52  
% 7.89/1.52  fof(f82,plain,(
% 7.89/1.52    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.89/1.52    inference(equality_resolution,[],[f65])).
% 7.89/1.52  
% 7.89/1.52  fof(f18,axiom,(
% 7.89/1.52    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 7.89/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.52  
% 7.89/1.52  fof(f26,plain,(
% 7.89/1.52    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 7.89/1.52    inference(ennf_transformation,[],[f18])).
% 7.89/1.52  
% 7.89/1.52  fof(f69,plain,(
% 7.89/1.52    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.89/1.52    inference(cnf_transformation,[],[f26])).
% 7.89/1.52  
% 7.89/1.52  fof(f52,plain,(
% 7.89/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.89/1.52    inference(cnf_transformation,[],[f34])).
% 7.89/1.52  
% 7.89/1.52  fof(f7,axiom,(
% 7.89/1.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.89/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.52  
% 7.89/1.52  fof(f25,plain,(
% 7.89/1.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.89/1.52    inference(ennf_transformation,[],[f7])).
% 7.89/1.52  
% 7.89/1.52  fof(f55,plain,(
% 7.89/1.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.89/1.52    inference(cnf_transformation,[],[f25])).
% 7.89/1.52  
% 7.89/1.52  fof(f3,axiom,(
% 7.89/1.52    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.89/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.52  
% 7.89/1.52  fof(f21,plain,(
% 7.89/1.52    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.89/1.52    inference(rectify,[],[f3])).
% 7.89/1.52  
% 7.89/1.52  fof(f48,plain,(
% 7.89/1.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.89/1.52    inference(cnf_transformation,[],[f21])).
% 7.89/1.52  
% 7.89/1.52  fof(f6,axiom,(
% 7.89/1.52    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 7.89/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.52  
% 7.89/1.52  fof(f23,plain,(
% 7.89/1.52    ! [X0,X1] : ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) => r3_xboole_0(X0,X1))),
% 7.89/1.52    inference(unused_predicate_definition_removal,[],[f6])).
% 7.89/1.52  
% 7.89/1.52  fof(f24,plain,(
% 7.89/1.52    ! [X0,X1] : (r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1)))),
% 7.89/1.52    inference(ennf_transformation,[],[f23])).
% 7.89/1.52  
% 7.89/1.52  fof(f53,plain,(
% 7.89/1.52    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.89/1.52    inference(cnf_transformation,[],[f24])).
% 7.89/1.52  
% 7.89/1.52  fof(f71,plain,(
% 7.89/1.52    ~r3_xboole_0(sK2,sK3)),
% 7.89/1.52    inference(cnf_transformation,[],[f40])).
% 7.89/1.52  
% 7.89/1.52  fof(f43,plain,(
% 7.89/1.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 7.89/1.52    inference(cnf_transformation,[],[f32])).
% 7.89/1.52  
% 7.89/1.52  fof(f77,plain,(
% 7.89/1.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 7.89/1.52    inference(equality_resolution,[],[f43])).
% 7.89/1.52  
% 7.89/1.52  fof(f54,plain,(
% 7.89/1.52    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 7.89/1.52    inference(cnf_transformation,[],[f24])).
% 7.89/1.52  
% 7.89/1.52  cnf(c_0,plain,
% 7.89/1.52      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.89/1.52      inference(cnf_transformation,[],[f41]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_22,plain,
% 7.89/1.52      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.89/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3709,plain,
% 7.89/1.52      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3818,plain,
% 7.89/1.52      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_0,c_3709]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_25,plain,
% 7.89/1.52      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.89/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3708,plain,
% 7.89/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_29,negated_conjecture,
% 7.89/1.52      ( k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) = k1_zfmisc_1(k2_xboole_0(sK2,sK3)) ),
% 7.89/1.52      inference(cnf_transformation,[],[f70]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_6,plain,
% 7.89/1.52      ( r2_hidden(X0,X1)
% 7.89/1.52      | r2_hidden(X0,X2)
% 7.89/1.52      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 7.89/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3713,plain,
% 7.89/1.52      ( r2_hidden(X0,X1) = iProver_top
% 7.89/1.52      | r2_hidden(X0,X2) = iProver_top
% 7.89/1.52      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4406,plain,
% 7.89/1.52      ( r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK2,sK3))) != iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(sK3)) = iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_29,c_3713]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4446,plain,
% 7.89/1.52      ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(sK3)) = iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3708,c_4406]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4644,plain,
% 7.89/1.52      ( r2_hidden(sK3,k1_zfmisc_1(sK3)) = iProver_top
% 7.89/1.52      | r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3818,c_4446]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_11,plain,
% 7.89/1.52      ( r1_tarski(X0,X0) ),
% 7.89/1.52      inference(cnf_transformation,[],[f80]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3711,plain,
% 7.89/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4642,plain,
% 7.89/1.52      ( r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK3)) = iProver_top
% 7.89/1.52      | r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3711,c_4446]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_26,plain,
% 7.89/1.52      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.89/1.52      inference(cnf_transformation,[],[f82]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3707,plain,
% 7.89/1.52      ( r1_tarski(X0,X1) = iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4710,plain,
% 7.89/1.52      ( r1_tarski(k2_xboole_0(sK2,sK3),sK3) = iProver_top
% 7.89/1.52      | r2_hidden(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_4642,c_3707]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4750,plain,
% 7.89/1.52      ( r1_tarski(k2_xboole_0(sK2,sK3),sK3) = iProver_top
% 7.89/1.52      | r1_tarski(k2_xboole_0(sK2,sK3),sK2) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_4710,c_3707]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_27,plain,
% 7.89/1.52      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 7.89/1.52      inference(cnf_transformation,[],[f69]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3706,plain,
% 7.89/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.89/1.52      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3858,plain,
% 7.89/1.52      ( r1_tarski(k1_zfmisc_1(sK3),k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_29,c_3818]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_9,plain,
% 7.89/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.89/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3712,plain,
% 7.89/1.52      ( X0 = X1
% 7.89/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.89/1.52      | r1_tarski(X1,X0) != iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4226,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK3)
% 7.89/1.52      | r1_tarski(k1_zfmisc_1(k2_xboole_0(sK2,sK3)),k1_zfmisc_1(sK3)) != iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3858,c_3712]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4285,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK3)
% 7.89/1.52      | r1_tarski(k2_xboole_0(sK2,sK3),sK3) != iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3706,c_4226]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_17925,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK3)
% 7.89/1.52      | r1_tarski(k2_xboole_0(sK2,sK3),sK2) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_4750,c_4285]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3821,plain,
% 7.89/1.52      ( r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_29,c_3709]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4225,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
% 7.89/1.52      | r1_tarski(k1_zfmisc_1(k2_xboole_0(sK2,sK3)),k1_zfmisc_1(sK2)) != iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3821,c_3712]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4270,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
% 7.89/1.52      | r1_tarski(k2_xboole_0(sK2,sK3),sK2) != iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3706,c_4225]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_18113,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK3)
% 7.89/1.52      | k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2) ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_17925,c_4270]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_14,plain,
% 7.89/1.52      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.89/1.52      inference(cnf_transformation,[],[f55]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3710,plain,
% 7.89/1.52      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3888,plain,
% 7.89/1.52      ( k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = k1_zfmisc_1(X1)
% 7.89/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3706,c_3710]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4812,plain,
% 7.89/1.52      ( k2_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK3)),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))) = k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))) ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3858,c_3888]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_5036,plain,
% 7.89/1.52      ( r1_tarski(k1_zfmisc_1(k1_zfmisc_1(sK3)),k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_4812,c_3709]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_5100,plain,
% 7.89/1.52      ( k2_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))))) = k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))) ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_5036,c_3888]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_18224,plain,
% 7.89/1.52      ( k2_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3))),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3)))) = k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3))))
% 7.89/1.52      | k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2) ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_18113,c_5100]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_7,plain,
% 7.89/1.52      ( k2_xboole_0(X0,X0) = X0 ),
% 7.89/1.52      inference(cnf_transformation,[],[f48]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_18325,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
% 7.89/1.52      | k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_xboole_0(sK2,sK3)))) = k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 7.89/1.52      inference(demodulation,[status(thm)],[c_18224,c_7]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_13,plain,
% 7.89/1.52      ( r3_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) ),
% 7.89/1.52      inference(cnf_transformation,[],[f53]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_28,negated_conjecture,
% 7.89/1.52      ( ~ r3_xboole_0(sK2,sK3) ),
% 7.89/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_285,plain,
% 7.89/1.52      ( ~ r1_tarski(X0,X1) | sK3 != X1 | sK2 != X0 ),
% 7.89/1.52      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_286,plain,
% 7.89/1.52      ( ~ r1_tarski(sK2,sK3) ),
% 7.89/1.52      inference(unflattening,[status(thm)],[c_285]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_287,plain,
% 7.89/1.52      ( r1_tarski(sK2,sK3) != iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4643,plain,
% 7.89/1.52      ( r2_hidden(sK2,k1_zfmisc_1(sK3)) = iProver_top
% 7.89/1.52      | r2_hidden(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3709,c_4446]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_37,plain,
% 7.89/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_39,plain,
% 7.89/1.52      ( r1_tarski(sK2,sK2) != iProver_top
% 7.89/1.52      | r2_hidden(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.89/1.52      inference(instantiation,[status(thm)],[c_37]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_65,plain,
% 7.89/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_67,plain,
% 7.89/1.52      ( r1_tarski(sK2,sK2) = iProver_top ),
% 7.89/1.52      inference(instantiation,[status(thm)],[c_65]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4679,plain,
% 7.89/1.52      ( r2_hidden(sK2,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.89/1.52      inference(global_propositional_subsumption,
% 7.89/1.52                [status(thm)],
% 7.89/1.52                [c_4643,c_39,c_67]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3890,plain,
% 7.89/1.52      ( k2_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = k1_zfmisc_1(k2_xboole_0(sK2,sK3)) ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3821,c_3710]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_5,plain,
% 7.89/1.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 7.89/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3714,plain,
% 7.89/1.52      ( r2_hidden(X0,X1) != iProver_top
% 7.89/1.52      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4159,plain,
% 7.89/1.52      ( r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(sK2)) != iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3890,c_3714]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_18238,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(sK3)) = iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(sK2)) != iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_18113,c_4159]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_19047,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
% 7.89/1.52      | r2_hidden(sK2,k1_zfmisc_1(sK3)) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_4679,c_18238]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_19105,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2)
% 7.89/1.52      | r1_tarski(sK2,sK3) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_19047,c_3707]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_19253,plain,
% 7.89/1.52      ( k1_zfmisc_1(k2_xboole_0(sK2,sK3)) = k1_zfmisc_1(sK2) ),
% 7.89/1.52      inference(global_propositional_subsumption,
% 7.89/1.52                [status(thm)],
% 7.89/1.52                [c_18325,c_287,c_19105]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_3891,plain,
% 7.89/1.52      ( k2_xboole_0(k1_zfmisc_1(sK3),k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = k1_zfmisc_1(k2_xboole_0(sK2,sK3)) ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3858,c_3710]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_4160,plain,
% 7.89/1.52      ( r2_hidden(X0,k1_zfmisc_1(k2_xboole_0(sK2,sK3))) = iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_3891,c_3714]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_19337,plain,
% 7.89/1.52      ( r2_hidden(X0,k1_zfmisc_1(sK3)) != iProver_top
% 7.89/1.52      | r2_hidden(X0,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.89/1.52      inference(demodulation,[status(thm)],[c_19253,c_4160]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_20981,plain,
% 7.89/1.52      ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_4644,c_19337]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_21009,plain,
% 7.89/1.52      ( r1_tarski(sK3,sK2) = iProver_top ),
% 7.89/1.52      inference(superposition,[status(thm)],[c_20981,c_3707]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_12,plain,
% 7.89/1.52      ( r3_xboole_0(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.89/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_292,plain,
% 7.89/1.52      ( ~ r1_tarski(X0,X1) | sK3 != X0 | sK2 != X1 ),
% 7.89/1.52      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_293,plain,
% 7.89/1.52      ( ~ r1_tarski(sK3,sK2) ),
% 7.89/1.52      inference(unflattening,[status(thm)],[c_292]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(c_294,plain,
% 7.89/1.52      ( r1_tarski(sK3,sK2) != iProver_top ),
% 7.89/1.52      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 7.89/1.52  
% 7.89/1.52  cnf(contradiction,plain,
% 7.89/1.52      ( $false ),
% 7.89/1.52      inference(minisat,[status(thm)],[c_21009,c_294]) ).
% 7.89/1.52  
% 7.89/1.52  
% 7.89/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.89/1.52  
% 7.89/1.52  ------                               Statistics
% 7.89/1.52  
% 7.89/1.52  ------ Selected
% 7.89/1.52  
% 7.89/1.52  total_time:                             0.672
% 7.89/1.52  
%------------------------------------------------------------------------------
